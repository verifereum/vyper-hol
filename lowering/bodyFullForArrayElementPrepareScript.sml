(* Indexed non-slot array element preparation at the live body-entry cursor. *)
Theory bodyFullForArrayElementPrepare
Ancestors bodyInvSplit bodyInvCodeProps bodyInvMetadataProps bodyInvExecutionProps compileUnit alist exprSimHyps[qualified,ignore_grammar]
  bodySingletonCallSupport vyperTypeCallGraph[qualified,ignore_grammar]
  bodyFullForMemoryElementDispatch bodyFullForImmutableElementInput bodyFullForArray
  typedCopyOriginPtrBase typedMemoryCopy stmtReasonLitFragMemory
  stmtSimForArrayLoop whitelistForIterDynLoop fragGasSeqPtr fragExecMem fragExec
  ptrDiscipline ptrSafeRun unitTransformDefs memSafeRun context
  venomInst venomState venomExecSemantics emitHelperProps loweringStateRelDefs
  compileEnv exprLoweringProps exprOperandVar finite_map list words arithmetic
  vyperTypeEnv[qualified,ignore_grammar] vyperPlaceTyping[qualified,ignore_grammar]
  stmtLoweringMono[qualified,ignore_grammar]

(* When a dead byte depends on a dynamic header, that header ends before
   the byte. No agreement at or beyond the byte under test is needed. *)
Theorem for_element_dead_prefix[local]:
  (!s off tv j t. mem_bytes_at 0 j s = mem_bytes_at 0 j t ==>
      (mem_dead_bytes s off tv j <=> mem_dead_bytes t off tv j)) /\
  (!s off tvs j t. mem_bytes_at 0 j s = mem_bytes_at 0 j t ==>
      (mem_dead_bytes_list s off tvs j <=> mem_dead_bytes_list t off tvs j)) /\
  (!s off fields j t. mem_bytes_at 0 j s = mem_bytes_at 0 j t ==>
      (mem_dead_bytes_fields s off fields j <=> mem_dead_bytes_fields t off fields j))
Proof
  `!s t off j. mem_bytes_at 0 j s = mem_bytes_at 0 j t /\ off + 32 <= j ==>
      mem_word_at off t = mem_word_at off s` by
    (rpt strip_tac >> simp[abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
     AP_TERM_TAC >> metis_tac[valueEncodingPropsTheory.mem_bytes_at_translated_window,
                            ADD_CLAUSES]) >>
  `!s off tv j n et.
      (tv = BaseTV (BytesT (Dynamic n)) \/ tv = BaseTV (StringT n) \/
       tv = ArrayTV et (Dynamic n)) /\ j < off + 32 ==>
      ~mem_dead_bytes s off tv j` by
    (rpt strip_tac >> Cases_on `j < off` >>
     metis_tac[ctorDeployDeadSectionTheory.mem_dead_bytes_header_live,
               cj 1 ctorDeployDeadSectionTheory.mem_dead_bytes_range, NOT_LESS]) >>
  ho_match_mp_tac immSectionDeadTheory.mem_dead_bytes_ind >>
  rpt conj_tac >> rpt strip_tac >>
  Cases_on `off + 32 <= j`
  >>~- ([`mem_dead_bytes _ _ (BaseTV (BytesT (Dynamic _))) _ <=> _`,
         `~(off + 32 <= j)`],
        `j < off + 32` by decide_tac >> metis_tac[])
  >>~- ([`mem_dead_bytes _ _ (BaseTV (StringT _)) _ <=> _`,
         `~(off + 32 <= j)`],
        `j < off + 32` by decide_tac >> metis_tac[])
  >>~- ([`mem_dead_bytes _ _ (ArrayTV _ (Dynamic _)) _ <=> _`,
         `~(off + 32 <= j)`],
        `j < off + 32` by decide_tac >> metis_tac[]) >>
  `off + 32 <= j ==> mem_word_at off t = mem_word_at off s` by metis_tac[] >>
  gvs[immSectionDeadTheory.mem_dead_bytes_def] >>
  (metis_tac[])
QED

(* Address arithmetic changes only the destination register and its ghosts.
   Use the incoming provenance even when ADD's destination aliases an input. *)
Theorem for_element_address_arithmetic[local]:
  (opc = MUL /\ w = x * y \/ opc = ADD /\ w = x + y) /\
  eval_operand left s = SOME x /\ eval_operand right s = SOME y /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  i = mk_inst iid opc [left;right] [out] /\ u = update_var out w s /\
  G' = step_prov PG G i u /\ tn' = step_taint i s u tn /\
  pv = (if opc = ADD then first_prov G [left;right] else NONE) ==>
  step_inst_base i s = OK u /\
  (!D. ptr_inst_ok D lo 0 ctx func G tn i s) /\
  inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
  op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = pv /\
  tn'.t_mem = tn.t_mem /\ tn'.t_imm = tn.t_imm /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
    op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `step_inst_base i s = OK u` by
    (gvs[] >>
     simp_tac std_ss [Once step_inst_base_def, mk_inst_def,
       instruction_accessors, instruction_accfupds, opcode_case_def] >>
     simp[exec_pure2_def]) >>
  `opc = MUL \/ opc = ADD` by metis_tac[] >>
  `(!D. ptr_inst_ok D lo 0 ctx func G tn i s) /\
   inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    (conj_tac >- (gen_tac >> gvs[] >>
      irule (cj 1 typed_copy_origin_ptr_binop_checks) >> metis_tac[]) >>
     gvs[] >> metis_tac[typed_copy_origin_ptr_binop_checks]) >>
  gvs[typed_copy_origin_ptr_binop_ghost_frame, op_prov_def] >>
  simp[step_prov_def, mk_inst_def, out_prov_def, set_prov_def] >>
  Cases_on `first_prov G [left;right]` >> simp[FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]
QED

(* The optional ADD is the only header adjustment. In both branches the
   final ADD reads [base], not a header-adjusted copy of it. *)
Theorem for_element_address_emission[local]:
  emit_op MUL [Var idx;Lit (n2w stride)] sa = (offOp,sm) /\
  (if dyn then emit_op ADD [Lit 32w;offOp] sm = (sumOp,sn)
   else sumOp = offOp /\ sn = sm) /\
  emit_op ADD [arr_op;sumOp] sn = (addr,sc) ==>
  ?ov hv ep.
    offOp = Var ov /\ sumOp = Var hv /\ addr = Var ep /\
    not_fresh_at sc ep /\ sc.cs_current_bb = sa.cs_current_bb /\
    (dyn ==> ov <> hv) /\
    (!p. not_fresh_at sa p ==> p <> ov /\ p <> hv /\ p <> ep) /\
    sc.cs_current_insts = sa.cs_current_insts ++
      (mk_inst sa.cs_next_id MUL [Var idx;Lit (n2w stride)] [ov] ::
       ((if dyn then [mk_inst sm.cs_next_id ADD [Lit 32w;Var ov] [hv]] else []) ++
        [mk_inst sn.cs_next_id ADD [arr_op;Var hv] [ep]]))
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  Cases_on `dyn` >> fs[] >>
  imp_res_tac loweringShapeRulesTheory.emit_op_facts >>
  imp_res_tac emitted_insts_emit_op >>
  gvs[] >> simp[GSYM APPEND_ASSOC, not_fresh_at_def] >> metis_tac[]
QED

(* The positioned intermediary keeps the same machine fields as the raw
   register update. It is used in the recursive instruction checks. *)
Theorem for_element_address_update[local]:
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  allocas_from lo (update_var out w s with vs_inst_idx := pc) /\
  (ctx_has_dalloca ctx ==>
    allocas_below_fmp (update_var out w s with vs_inst_idx := pc))
Proof
  simp[allocas_from_def, allocas_below_fmp_def, update_var_def] >> metis_tac[]
QED

Theorem for_element_address_operand_frame[local]:
  (!p. op = Var p ==> p <> out) /\
  (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
                    op_taint tn' (Var p) = op_taint tn (Var p)) ==>
  eval_operand op (update_var out w s with vs_inst_idx := pc) = eval_operand op s /\
  op_prov G' op = op_prov G op /\ op_taint tn' op = op_taint tn op
Proof
  Cases_on `op` >> simp[eval_operand_def, op_prov_def, op_taint_def,
    lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem for_element_address_prefix[local]:
  emit_op MUL [Var idx;Lit (n2w stride)] sa = (offOp,sm) /\
  (if dyn then emit_op ADD [Lit 32w;offOp] sm = (sumOp,sn)
   else sumOp = offOp /\ sn = sm) /\
  emit_op ADD [arr_op;sumOp] sn = (addr,sc) /\
  fn_has_code sa sc func /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand arr_op s = SOME bw /\
  (!p. arr_op = Var p ==> not_fresh_at sa p) /\
  op_taint tn (Var idx) = {} /\ op_taint tn arr_op = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out t Gf tnf.
    addr = Var out /\ not_fresh_at sc out /\
    lookup_var out t = SOME (bw + n2w ((if dyn then 32 else 0) + k*stride)) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = op_prov G arr_op /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!off len. typed_copy_state_frame sa off len s t) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!p. op_taint tn (Var p) = {} ==> op_taint tnf (Var p) = {})
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  drule_all for_element_address_emission >>
  disch_then (qx_choose_then `ov` (qx_choose_then `hv` (qx_choose_then `ep` strip_assume_tac))) >>
  gvs[] >>
  qabbrev_tac `i1 = mk_inst sa.cs_next_id MUL [Var idx;Lit (n2w stride)] [ov]` >>
  qabbrev_tac `ih = mk_inst sm.cs_next_id ADD [Lit 32w;Var ov] [hv]` >>
  qabbrev_tac `ie = mk_inst sn.cs_next_id ADD [arr_op;Var hv] [ep]` >>
  qabbrev_tac `code = i1 :: ((if dyn then [ih] else []) ++ [ie])` >>
  `sc.cs_current_insts = sa.cs_current_insts ++ code` by
    simp[Abbr`code`] >>
  drule_all fn_has_code_code >> strip_tac >>
  qabbrev_tac `u1 = update_var ov (n2w (k*stride)) s` >>
  qabbrev_tac `s1 = u1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = step_prov PG G i1 u1` >>
  qabbrev_tac `tn1 = step_taint i1 s u1 tn` >>
  `eval_operand (Var idx) s = SOME (n2w k)` by simp[eval_operand_def] >>
  `eval_operand (Lit (n2w stride)) s = SOME (n2w stride)` by simp[eval_operand_def] >>
  `op_taint tn (Lit (n2w stride)) = {}` by simp[op_taint_def] >>
  `step_inst_base i1 s = OK u1 /\ (!D. ptr_inst_ok D lo 0 ctx func G tn i1 s) /\
   inst_mem_below_frontier i1 s /\ inst_dload_in_section i1 s /\
   op_taint tn1 (Var ov) = {} /\ op_prov G1 (Var ov) = NONE /\
   tn1.t_mem = tn.t_mem /\ tn1.t_imm = tn.t_imm /\
   tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\
   (!p. p <> ov ==> FLOOKUP G1 p = FLOOKUP G p /\
                    op_taint tn1 (Var p) = op_taint tn (Var p))` by
    (MATCH_MP_TAC (GEN_ALL (Q.INST [`opc` |-> `MUL`] for_element_address_arithmetic)) >>
     qexistsl [`n2w stride`, `n2w k`, `n2w (k*stride)`,
               `Lit (n2w stride)`, `Var idx`, `sa.cs_next_id`, `PG`] >>
     simp[Abbr`i1`, Abbr`u1`, Abbr`G1`, Abbr`tn1`, word_mul_n2w]) >>
  `allocas_from lo s1 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s1)` by
    (simp[Abbr`s1`, Abbr`u1`] >> metis_tac[for_element_address_update]) >>
  `!p. arr_op = Var p ==> p <> ov` by metis_tac[] >>
  drule_all for_element_address_operand_frame >> strip_tac >>
  `eval_operand arr_op s1 = SOME bw /\
   op_prov G1 arr_op = op_prov G arr_op /\ op_taint tn1 arr_op = {}` by
    simp[Abbr`s1`, Abbr`u1`] >>
  suspend "offset"
QED

Resume for_element_address_prefix[offset]:
  `!p. op_taint tn (Var p) = {} ==> op_taint tn1 (Var p) = {}` by
    (qx_gen_tac `x` >> Cases_on `x = ov` >> simp[]) >>
  `eval_operand (Var ov) s1 = SOME (n2w (k*stride))` by
    simp[Abbr`s1`, Abbr`u1`, eval_operand_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE] >>
  `get_instruction bb s.vs_inst_idx = SOME i1 /\
   isPREFIX ((if dyn then [ih] else []) ++ [ie])
     (DROP (SUC s.vs_inst_idx) bb.bb_instructions)` by
    (irule fragGasSeqAbortTheory.instruction_prefix_cursor >>
     qpat_x_assum `isPREFIX code _` mp_tac >> simp[Abbr`code`]) >>
  `!D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
             (OK s1,G1,tn1)` by
    (gen_tac >>
     mp_tac (Q.INST [`i` |-> `i1`, `u` |-> `u1`] straight_line_origin_ptr_edge) >>
     simp[Abbr`s1`, Abbr`G1`, Abbr`tn1`, Abbr`u1`, Abbr`i1`,
          mk_inst_def, instruction_accessors, instruction_accfupds,
          is_terminator_def]) >>
  suspend "header"
QED

Resume for_element_address_prefix[header]:
  `!off len. typed_copy_state_frame sa off len s s1` by
    simp[typed_copy_state_frame_def, Abbr`s1`, Abbr`u1`, update_var_def,
         lookup_var_def, FLOOKUP_UPDATE, venom_state_component_equality] >>
  `~s1.vs_halted /\ s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_inst_idx = SUC s.vs_inst_idx` by
    simp[Abbr`s1`, Abbr`u1`, update_var_def] >>
  qmatch_goalsub_abbrev_tac `SOME (bw + delta)` >>
  `?s2 G2 tn2.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s1,G1,tn1) []
                                  (OK s2,G2,tn2)) /\
      ~s2.vs_halted /\ s2.vs_current_bb = s.vs_current_bb /\
      s2.vs_inst_idx = s.vs_inst_idx + (if dyn then 2 else 1) /\
      get_instruction bb s2.vs_inst_idx = SOME ie /\
      eval_operand (Var hv) s2 = SOME delta /\ op_taint tn2 (Var hv) = {} /\
      op_prov G2 (Var hv) = NONE /\
      eval_operand arr_op s2 = SOME bw /\ op_taint tn2 arr_op = {} /\
      op_prov G2 arr_op = op_prov G arr_op /\
      allocas_from lo s2 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s2) /\
      (!off len. typed_copy_state_frame sa off len s1 s2) /\
      s2.vs_memory = s1.vs_memory /\ s2.vs_alloca_next = s1.vs_alloca_next /\
      tn2.t_mem = tn1.t_mem /\ tn2.t_imm = tn1.t_imm /\
      tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\
      (!p. not_fresh_at sa p ==>
        FLOOKUP G2 p = FLOOKUP G1 p /\ op_taint tn2 (Var p) = op_taint tn1 (Var p)) /\
      (!p. op_taint tn1 (Var p) = {} ==> op_taint tn2 (Var p) = {})` by
    (Cases_on `dyn`
     >- suspend "header_present"
     >> qexistsl [`s1`, `G1`, `tn1`] >> fs[Abbr`delta`] >>
     simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules, typed_copy_state_frame_def] >>
     `get_instruction bb (SUC s.vs_inst_idx) = SOME ie` by
       metis_tac[fragGasSeqAbortTheory.instruction_prefix_cursor] >>
     pop_assum mp_tac >> simp[ADD1]) >>
  suspend "final_add"
QED

Resume for_element_address_prefix[header_present]:
  `isPREFIX [ih;ie] (DROP s1.vs_inst_idx bb.bb_instructions)` by
    gvs[] >>
  drule_then strip_assume_tac fragGasSeqAbortTheory.instruction_prefix_cursor >>
  `get_instruction bb (SUC s1.vs_inst_idx) = SOME ie` by
    (irule (cj 1 fragGasSeqAbortTheory.instruction_prefix_cursor) >>
     qexists_tac `[]` >> simp[]) >>
  qabbrev_tac `uh = update_var hv delta s1` >>
  qabbrev_tac `sh = uh with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `Gh = step_prov PG G1 ih uh` >>
  qabbrev_tac `tnh = step_taint ih s1 uh tn1` >>
  `step_inst_base ih s1 = OK uh /\ (!D. ptr_inst_ok D lo 0 ctx func G1 tn1 ih s1) /\
   inst_mem_below_frontier ih s1 /\ inst_dload_in_section ih s1 /\
   op_taint tnh (Var hv) = {} /\ op_prov Gh (Var hv) = NONE /\
   tnh.t_mem = tn1.t_mem /\ tnh.t_imm = tn1.t_imm /\
   tnh.t_stor = tn1.t_stor /\ tnh.t_trans = tn1.t_trans /\
   (!p. p <> hv ==> FLOOKUP Gh p = FLOOKUP G1 p /\
                    op_taint tnh (Var p) = op_taint tn1 (Var p))` by
    (MATCH_MP_TAC (GEN_ALL (Q.INST [`opc` |-> `ADD`] for_element_address_arithmetic)) >>
     qexistsl [`n2w (k*stride)`, `32w`, `delta`, `Var ov`, `Lit 32w`,
               `sm.cs_next_id`, `PG`] >>
     simp[Abbr`ih`, Abbr`uh`, Abbr`Gh`, Abbr`tnh`, Abbr`delta`, word_add_n2w,
          eval_operand_def, op_taint_def, first_prov_def, op_prov_def]) >>
  suspend "header_join"
QED

Resume for_element_address_prefix[header_join]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s1,G1,tn1) []
            (OK sh,Gh,tnh)` by
    (gen_tac >>
     `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s1,G1,tn1) []
                          (OK sh,Gh,tnh)` by
       (mp_tac (Q.INST [`i` |-> `ih`, `u` |-> `uh`, `s` |-> `s1`,
                       `G` |-> `G1`, `tn` |-> `tn1`] straight_line_origin_ptr_edge) >>
        gvs[Abbr`sh`, Abbr`Gh`, Abbr`tnh`, Abbr`ih`,
            mk_inst_def, instruction_accessors, instruction_accfupds,
            is_terminator_def]) >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sh,Gh,tnh) []
                          (OK sh,Gh,tnh)` by
       (irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
        simp[Abbr`sh`, Abbr`uh`, update_var_def]) >>
     drule_all (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]) >>
  `!p. arr_op = Var p ==> p <> hv` by metis_tac[] >>
  drule_all for_element_address_operand_frame >>
  disch_then (qspecl_then [`delta`, `s1`, `SUC s1.vs_inst_idx`] strip_assume_tac) >>
  `!p. op_taint tn1 (Var p) = {} ==> op_taint tnh (Var p) = {}` by
    (qx_gen_tac `x` >> Cases_on `x = hv` >> simp[]) >>
  qexistsl [`sh`, `Gh`, `tnh`] >>
  simp[Abbr`sh`, Abbr`uh`, update_var_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, ADD1, typed_copy_state_frame_def, venom_state_component_equality] >>
  `SUC s1.vs_inst_idx = LENGTH sa.cs_current_insts + 2` by
    (asm_rewrite_tac[] >> decide_tac) >>
  fs[]
QED

Resume for_element_address_prefix[final_add]:
  rename1 `get_instruction bb s2.vs_inst_idx = SOME ie` >>
  rename1 `op_prov G2 (Var hv) = NONE` >>
  rename1 `op_taint tn2 (Var hv) = {}` >>
  qabbrev_tac `ue = update_var ep (bw + delta) s2` >>
  qabbrev_tac `se = ue with vs_inst_idx := SUC s2.vs_inst_idx` >>
  qabbrev_tac `Ge = step_prov PG G2 ie ue` >>
  qabbrev_tac `tne = step_taint ie s2 ue tn2` >>
  `first_prov G2 [arr_op;Var hv] = op_prov G2 arr_op` by
    (simp[first_prov_def] >> Cases_on `op_prov G arr_op` >> simp[]) >>
  `step_inst_base ie s2 = OK ue /\ (!D. ptr_inst_ok D lo 0 ctx func G2 tn2 ie s2) /\
   inst_mem_below_frontier ie s2 /\ inst_dload_in_section ie s2 /\
   op_taint tne (Var ep) = {} /\ op_prov Ge (Var ep) = op_prov G arr_op /\
   tne.t_mem = tn2.t_mem /\ tne.t_imm = tn2.t_imm /\
   tne.t_stor = tn2.t_stor /\ tne.t_trans = tn2.t_trans /\
   (!p. p <> ep ==> FLOOKUP Ge p = FLOOKUP G2 p /\
                    op_taint tne (Var p) = op_taint tn2 (Var p))` by
    (MATCH_MP_TAC (GEN_ALL (Q.INST [`opc` |-> `ADD`] for_element_address_arithmetic)) >>
     qexistsl [`delta`, `bw`, `bw + delta`, `Var hv`, `arr_op`, `sn.cs_next_id`, `PG`] >>
     simp[Abbr`ie`, Abbr`ue`, Abbr`Ge`, Abbr`tne`]) >>
  suspend "end_frame"
QED

Resume for_element_address_prefix[end_frame]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
                          (OK se,Ge,tne)` by
    (gen_tac >>
     `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s2,G2,tn2) []
                          (OK se,Ge,tne)` by
       (mp_tac (Q.INST [`i` |-> `ie`, `u` |-> `ue`, `s` |-> `s2`,
                        `G` |-> `G2`, `tn` |-> `tn2`] straight_line_origin_ptr_edge) >>
        gvs[Abbr`se`, Abbr`Ge`, Abbr`tne`, Abbr`ie`,
            mk_inst_def, instruction_accessors, instruction_accfupds,
            is_terminator_def]) >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (se,Ge,tne) []
                          (OK se,Ge,tne)` by
       (irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
        simp[Abbr`se`, Abbr`ue`, update_var_def]) >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s2,G2,tn2) []
                         (OK se,Ge,tne)` by
       (drule_all (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]) >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s1,G1,tn1) []
                         (OK se,Ge,tne)` by
       (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
        qexistsl [`G2`,`s2`,`tn2`] >> simp[]) >>
     qpat_assum `!dd. gas_origin_ptr_edge _ (s,G,tn) [] _`
       (qspec_then `D` (mp_then Any mp_tac
                        (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules))) >>
     disch_then drule >> simp[]) >>
  `!off len. typed_copy_state_frame sa off len s2 se` by
    simp[typed_copy_state_frame_def, Abbr`se`, Abbr`ue`, update_var_def,
         lookup_var_def, FLOOKUP_UPDATE, venom_state_component_equality] >>
  `!off len. typed_copy_state_frame sa off len s se` by
    (rpt gen_tac >> irule typed_copy_state_frame_trans >> qexists_tac `s2` >>
     simp[] >> irule typed_copy_state_frame_trans >> qexists_tac `s1` >> simp[]) >>
  `s1.vs_memory = s.vs_memory /\ s1.vs_alloca_next = s.vs_alloca_next` by
    simp[Abbr`s1`, Abbr`u1`, update_var_def] >>
  `se.vs_inst_idx = LENGTH sc.cs_current_insts` by
    (qpat_assum `sc.cs_current_insts = sa.cs_current_insts ++ code` mp_tac >>
     Cases_on `dyn` >> simp[Abbr`code`, Abbr`se`, ADD1] >> decide_tac) >>
  `n2w ((if dyn then 32 else 0) + k * stride) = delta` by
    simp[Abbr`delta`, Once ADD_COMM] >>
  `!p. op_taint tn2 (Var p) = {} ==> op_taint tne (Var p) = {}` by
    (qx_gen_tac `x` >> Cases_on `x = ep` >> simp[]) >>
  `!p. op_taint tn (Var p) = {} ==> op_taint tne (Var p) = {}` by
    (rpt strip_tac >> simp[]) >>
  qexistsl [`se`,`Ge`,`tne`] >>
  simp[Abbr`se`, Abbr`ue`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `dyn` >> simp[Abbr`code`] >> decide_tac
QED

Finalise for_element_address_prefix[local]

(* The copy changes memory and register ghosts, but leaves the
   storage, transient and code observations of every dead mask intact. *)
Theorem for_element_copy_ghost_horizon[local]:
  ghost_inv_at D0 lo d bc cx ee Gf tnf t /\
  ghost_inv_at D lo d c cx es G tn s /\
  copy_static t = copy_static s /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm ==>
  ghost_inv_at D lo d bc cx ee Gf tnf t
Proof
  simp[bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.stor_taint_ok_at_def,
       exprSimStorageCopyTheory.copy_static_def, venom_state_component_equality] >>
  strip_tac >> fs[]
QED

(* The expression/length endpoint (em,u,Gu,tu) is the capture anchor.
   (es0,sa0,s0,G0,tn0) is the older anchor of the whole For fragment. *)
Theorem for_nonslot_array_element_prepare_full:
  body_inv tops ctx c cx /\ expr_sim_inv c cx env es /\
  supported_stmt tops bindings (For id fty (Array e) bound loop_body) /\
  type_stmt env ret_ty (For id fty (Array e) bound loop_body) = SOME env' /\
  stmt_exprs_ok c (For id fty (Array e) bound loop_body) /\
  evaluate_type (get_tenv cx) fty = SOME dtv /\
  expr_type e = ArrayT sty bd /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV stv bd) /\
  compile_expr c (expr_type e) e sa0 = (vv,sbExpr) /\
  read_result cx rv em = (INL (ArrayV av),em) /\
  (rv = Value (ArrayV av) ==> value_has_type (ArrayTV stv bd) (ArrayV av)) /\
  extract_elements (ArrayTV stv bd) (ArrayV av) = SOME xs /\
  vs = MAP Value xs /\ k < LENGTH vs /\
  vv_store_bound cx (post_value_type c e) (lowered_value_type c e) em rv vv u /\
  ptr_vv_ok cx (post_value_type c e) rv vv em Gu tu u /\
  (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
    ~is_bytestring_type (post_value_type c e) ==>
    vv_own c cx (post_value_type c e) sa0 sbExpr em rv vv u /\
    (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
  (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
      eval_operand (vv_operand vv) u = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
        val_in_memory rt (ArrayV av) (w2n w) mem)) /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type c e) ==>
    ptr_buf_ok c e op Gu u) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok c e p.ptr_operand Gu u) /\
  loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
  (loc = LocMemory \/ loc = LocCode) /\
  (loc = LocMemory ==> rv = Value (ArrayV av) \/
    ?name path. rv = PlaceR (MemoryPlace name path)) /\
  (loc = LocMemory ==> !name path. rv = PlaceR (MemoryPlace name path) ==>
    OPTION_MAP (\entry. (entry.type,evaluate_subscripts entry.type entry.value path))
      (lookup_scopes name es.scopes) =
    OPTION_MAP (\entry. (entry.type,evaluate_subscripts entry.type entry.value path))
      (lookup_scopes name em.scopes)) /\
  (loc = LocCode ==>
    immutable_holds c cx (post_value_type c e) (Value (ArrayV av)) bw es s) /\
  (!name path. rv = PlaceR (MemoryPlace name path) ==>
    runtime_place_typed cx em (MemoryPlace name path) (ArrayTV stv bd)) /\
  (!name path. rv = PlaceR (MemoryPlace name path) ==>
    ?entry. lookup_scopes name em.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) /\
  (!name path root sz w. rv = PlaceR (MemoryPlace name path) /\
    FLOOKUP c.ce_vars name = SOME (PtrVar (Var root) sz) /\
    lookup_var root u = SOME w ==> lookup_var root s = SOME w) /\
  alloca_frame c em sbExpr u c es s /\
  (!aid r. FLOOKUP u.vs_allocas aid = SOME r ==> FLOOKUP s.vs_allocas aid = SOME r) /\
  (!aid b len i. FLOOKUP u.vs_allocas aid = SOME (b,len) /\
    aid < sbExpr.cs_next_id /\
    (!name lb lsz. local_region c em.scopes u name lb lsz ==>
      b + len <= lb \/ lb + lsz <= b) /\
    b <= i /\ i < b + len /\ i IN tn.t_mem ==> i IN tu.t_mem) /\
  eval_operand (vv_operand vv) u = SOME bw /\
  eval_operand (vv_operand vv) s = SOME bw /\
  op_prov G (vv_operand vv) = op_prov Gu (vv_operand vv) /\
  op_taint tn (vv_operand vv) = {} /\
  (!p. vv_operand vv = Var p ==> not_fresh_at sa p) /\
  lookup_var idx s = SOME (n2w k) /\ op_taint tn (Var idx) = {} /\
  stride = elem_size_in_location c loc sty /\
  dyn = (case bd of Fixed _ => F | Dynamic _ => T) /\
  emit_op MUL [Var idx;Lit (n2w stride)] sa = (offOp,sm) /\
  (if (if dyn then word_scale loc else 0) > 0 then
     emit_op ADD [Lit (n2w (if dyn then word_scale loc else 0));offOp] sm = (sumOp,sn)
   else sumOp = offOp /\ sn = sm) /\
  emit_op ADD [vv_operand vv;sumOp] sn = (addr,saCopy) /\
  compile_iter_elem_copy c addr (Var xd) stride loc (is_slot_addressed loc) fty sty
    saCopy = ((),sbCopy) /\
  fn_has_code sa saCopy func /\ fn_has_code saCopy sbCopy func /\
  fn_inst_ids_distinct func /\
  cenv_top_ext c bc (FEMPTY :: es.scopes) /\
  local_ptrs_reserved c sa /\
  local_ptrs_reserved c saCopy /\ local_ptrs_reserved bc sbCopy /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at saCopy x) /\
  not_fresh_at sa xd /\ not_fresh_at saCopy xd /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var xd) capacity) /\
  (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP c.ce_vars name) /\
  lookup_scopes id es.scopes = NONE /\
  capacity = type_memory_size dtv /\
  sa0.cs_next_id <= aidItem /\ sbExpr.cs_next_id <= aidItem /\ aidItem < sa.cs_next_id /\
  FLOOKUP s.vs_allocas aidItem = SOME (w2n dw,capacity) /\
  (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_outputs = [xd] /\ inst.inst_id = aidItem) /\
  lookup_var xd s = SOME dw /\ ptr_covers G tn xd s capacity /\
  alloca_frame c es0 sa0 s0 c es s /\
  alloca_frame c es0 sa0 s0 bc (es with scopes updated_by CONS FEMPTY) s /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!x. not_fresh_at sa0 x ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa0 x ==>
    FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < sa0.cs_next_id /\
    (!name b len. local_region c es0.scopes s0 name b len ==>
      off + sz <= b \/ b + len <= off) /\
    off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    vv_post H ctx func c cx e es0 sa0 sbExpr s0 em rv vv u /\
    stmt_state_rel H ctx func c cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d c cx es G tn s) /\
  return_buf_frame d c sa s /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v ee t Gf tnf.
    read_result cx (EL k vs) es = (INL v,es) /\
    value_has_type dtv v /\ val_wf dtv v /\
    push_scope_with_var id dtv v es = (INL (),ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sbCopy.cs_current_bb /\
    t.vs_inst_idx = LENGTH sbCopy.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    FLOOKUP t.vs_allocas aidItem = SOME (w2n dw,capacity) /\
    lookup_var xd t = SOME dw /\ ptr_covers Gf tnf xd t capacity /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func bc cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d bc cx ee Gf tnf t) /\
    return_buf_frame d bc sbCopy t /\
    alloca_history func t /\ allocas_from lo t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    alloca_frame c es0 sa0 s0 bc ee t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    typed_copy_frame (w2n dw) capacity s.vs_memory t.vs_memory /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + capacity) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
    (!x. not_fresh_at sa0 x ==>
      FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
    (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < sa0.cs_next_id /\
      (!name b len. local_region c es0.scopes s0 name b len ==>
        off + sz <= b \/ b + len <= off) /\
      off <= i /\ i < off + sz /\ i IN tnf.t_mem ==> i IN tn0.t_mem)
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H = storage_trace_horizon es.storage_trace` >>
  `valid_horizon cx st0 H es.storage_trace` by
    fs[Abbr `H`, vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `D = DF H` >>
  `word_scale loc = 32` by
    (qpat_assum `loc = LocMemory \/ loc = LocCode` (DISJ_CASES_THEN SUBST1_TAC) >>
     simp[word_scale_def]) >>
  `(if dyn then emit_op ADD [Lit 32w;offOp] sm = (sumOp,sn)
    else sumOp = offOp /\ sn = sm)` by
    (Cases_on `dyn` >> fs[]) >>
  drule_all for_element_address_prefix >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choose_then `out` (qx_choose_then `sCopy`
      (qx_choose_then `GCopy` (qx_choose_then `tnCopy` strip_assume_tac))))) >>
  suspend "at_copy"
QED

Resume for_nonslot_array_element_prepare_full[at_copy]:
  `vs = MAP Value (array_elements (ArrayTV stv bd) av)` by
    fs[vyperValueOperationTheory.extract_elements_def] >>
  drule bodyFullForFactsTheory.type_stmt_for_projection >> strip_tac >>
  `sty = fty` by
    (qpat_x_assum `well_typed_iterator _ _ _` mp_tac >>
     simp[vyperTypeSystemTheory.well_typed_iterator_def]) >>
  `stv = dtv` by
    (drule memoryValueAbiStaticTheory.evaluate_type_ArrayTV_result >>
     fs[] >> metis_tac[]) >>
  `post_value_type c e = expr_type e` by
    (drule bodyFullForFactsTheory.supported_stmt_for_projection >> strip_tac >>
     irule bodySimDeclCasesTheory.post_value_type_declared_return >>
     qexists_tac `tops` >>
     `supported_program tops /\ c.ce_func_return_type = build_func_return_type tops` by
       (drule_then assume_tac bodySimTheory.body_inv_contract >>
        drule_then assume_tac bodySimTheory.body_inv_module >>
        drule_all_then strip_assume_tac contract_inv_module_gate >>
        drule_then assume_tac contract_inv_return_types >>
        fs[compileUnitTheory.build_func_return_type_mods_singleton]) >> simp[] >>
     rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     `well_typed_expr env (Call t (IntCall fid) args drv)` by
       fs[vyperTypeSystemTheory.well_typed_iterator_def] >>
     `FST fid = NONE` by
       (drule_all_then mp_tac (Q.INST [`e` |-> `Call t (IntCall fid) args drv`]
          body_inv_typed_calls_main) >>
        simp[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
     qpat_x_assum `supported_iterator _ _ (Array _) _` mp_tac >>
     Cases_on `supported_function_decl tops fid Internal` >>
     simp[supportedStmtsTheory.supported_iterator_def] >>
     rename1 `supported_function_decl _ _ _ = SOME decl` >>
     PairCases_on `decl` >> simp[]) >>
  `type_memory_bytes c fty = type_memory_size dtv` by
    ((drule_all exprSimHypsTheory.expr_sim_inv_memory_size >> simp[] >> (metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size]))) >>
  `stride = type_memory_size dtv` by
    (qpat_assum `loc = LocMemory \/ loc = LocCode` (DISJ_CASES_THEN SUBST1_TAC) >>
     fs[elem_size_in_location_def,is_slot_addressed_def]) >>
  qpat_assum `!off len. typed_copy_state_frame sa off len s sCopy`
    (qspecl_then [`0`,`0`]
      (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def])) >>
  qpat_assum `(sCopy with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
     vs_current_bb := _; vs_inst_idx := _|>) = s`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `FLOOKUP sCopy.vs_allocas aidItem = SOME (w2n dw,capacity) /\
   lookup_var xd sCopy = SOME dw` by simp[] >>
  `ptr_covers GCopy tnCopy xd sCopy capacity` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl [`G`,`s`,`tn`] >> simp[]) >>
  suspend "representation"
QED

Resume for_nonslot_array_element_prepare_full[representation]:
  `sCopy = (s with vs_vars := sCopy.vs_vars) with
     <|vs_prev_bb := sCopy.vs_prev_bb; vs_current_bb := sCopy.vs_current_bb;
       vs_inst_idx := sCopy.vs_inst_idx|>` by
    simp[venom_state_component_equality] >>
  `!(HH:(bool # bytes32 # type_value) list # num list). stmt_state_rel HH ctx func c cx es s ==>
    stmt_state_rel HH ctx func c cx es (s with vs_vars := sCopy.vs_vars)` by
    (gen_tac >> disch_tac >> irule exprSimPropsTheory.stmt_state_rel_vars_frame >>
     simp[] >>
     qpat_assum `local_ptrs_reserved c sa`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     conj_tac
     >- (rpt strip_tac >>
         `not_fresh_at sa p` by
           (qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP c.ce_vars n1 = _ ==> _`
              drule >> simp[]) >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x sCopy = _`
           (drule_then (mp_tac o REWRITE_RULE [lookup_var_def])) >> simp[lookup_var_def]) >>
     rpt strip_tac >>
     `not_fresh_at sa p` by
       (qpat_assum `!x. c.ce_imm_alloca = SOME (Var x) ==> _`
          (qspec_then `p` mp_tac) >> simp[]) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x sCopy = _`
       (drule_then (mp_tac o REWRITE_RULE [lookup_var_def])) >> simp[lookup_var_def]) >>
  `!(HH:(bool # bytes32 # type_value) list # num list). stmt_state_rel HH ctx func c cx es s ==>
      stmt_state_rel HH ctx func c cx es sCopy` by
    (qpat_assum `sCopy = _ with <|vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|>`
       (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[bodyPtrMakeArrayCopyStateFrameTheory.literal_stmt_state_rel_cursor]) >>
  `stmt_state_rel H ctx func c cx es sCopy` by
    (qpat_assum `!(HH:(bool # bytes32 # type_value) list # num list). _ ==> stmt_state_rel HH _ _ _ _ _ sCopy`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
          ptr_covers GCopy tnCopy p sCopy sz` by
    (rpt strip_tac >> irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl [`G`,`s`,`tn`] >> simp[]) >>
  `ghost_inv_at D lo d c cx es GCopy tnCopy sCopy` by
    (qpat_assum `ghost_inv_at D lo d c cx es G tn s`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     qpat_assum `local_ptrs_reserved c sa`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     `stor_taint_ok_at D tnCopy sCopy` by
       (qpat_x_assum `stor_taint_ok_at D tn s` mp_tac >>
        simp[bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
     `allocas_from lo sCopy` by
       (qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         `not_fresh_at sa p` by
           (qpat_assum `!n1 n2 x sz1 sz2. FLOOKUP c.ce_vars n1 = _ ==> _`
              drule >> simp[]) >>
         qpat_assum `!name entry p sz. lookup_scopes name es.scopes = _ /\ _ ==> _`
           (drule_all_then strip_assume_tac) >> simp[]) >>
     Cases_on `d` >- simp[bodyPtrDefsTheory.return_buf_ptr_def] >>
     rename1 `return_buf_ptr (SOME rb) _ _ _ _` >> PairCases_on `rb` >>
     qpat_x_assum `return_buf_frame (SOME _) c sa s`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.return_buf_frame_def]) >>
     qpat_x_assum `return_buf_ptr (SOME _) c G tn s`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.return_buf_ptr_def]) >>
     simp[bodyPtrDefsTheory.return_buf_ptr_def] >>
     fs[] >> metis_tac[]) >>
  qpat_assum `loc = LocMemory \/ loc = LocCode` DISJ_CASES_TAC
  >- suspend "memory_source"
  >> suspend "immutable_source"
QED

Resume for_nonslot_array_element_prepare_full[immutable_source]:
  `?ty p. vv = LocatedValue ty p /\ p.ptr_location = LocCode` by
    (Cases_on `vv` >> fs[vv_location_def]) >>
  `immutable_holds c cx (post_value_type c e) (Value (ArrayV av)) bw es sCopy` by
    (qpat_assum `loc = LocCode ==> immutable_holds c cx _ _ bw es s`
       (fn th => qpat_assum `loc = LocCode` (mp_tac o MATCH_MP th)) >>
     simp[NoAsms, loweringPostsTheory.immutable_holds_def]) >>
  `op_prov GCopy (Var out) = NONE` by
    fs[bodyPtrDefsTheory.ptr_vv_ok_def, vv_operand_def] >>
  suspend "immutable_input"
QED

Resume for_nonslot_array_element_prepare_full[immutable_input]:
  `c.ce_is_ctor ==> w2n bw + type_memory_size (ArrayTV stv bd) <= lo /\
     !mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
       val_in_memory (ArrayTV stv bd) (ArrayV av) (w2n bw) mem` by
    (disch_tac >>
     `vv_location vv = SOME LocCode` by fs[vv_location_def] >>
     `evaluate_type (get_tenv cx) (ArrayT fty bd) = SOME (ArrayTV dtv bd)` by
       (qpat_assum `expr_type e = ArrayT sty bd` (fn th =>
          qpat_assum `evaluate_type (get_tenv cx) (expr_type e) = _`
            (mp_tac o REWRITE_RULE [th])) >> simp[]) >>
     qpat_x_assum `c.ce_is_ctor /\ vv_location vv = SOME LocCode ==> !rt w. _`
       mp_tac >> simp[]) >>
  `lookup_var out sCopy = SOME
    (bw + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + k * stride))` by
    (Cases_on `bd` >> fs[]) >>
  `!region x. c.ce_imm_alloca = SOME region /\ region = Var x ==>
    not_fresh_at saCopy x` by
    metis_tac[local_ptrs_reserved_imm_base] >>
  `stride = elem_size_in_location c LocCode sty` by
    simp[elem_size_in_location_def,is_slot_addressed_def] >>
  `read_result cx (Value (ArrayV av)) es = (INL (ArrayV av),es)` by
    simp[vyperStateTheory.read_result_def,vyperStateTheory.return_def] >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
  `expr_type e = ArrayT fty bd /\ sty = fty /\
   evaluate_type (get_tenv cx) fty = SOME stv /\
   stride = type_memory_size stv /\
   (stride = 32 \/ ?q. stride = 32 * q /\ 32 < stride) /\
   w2n dw + capacity < dimword (:256) /\
   ?v a. EL k vs = Value v /\ value_has_type stv v /\ val_wf stv v /\
     immutable_holds c cx fty (Value v) a es sCopy /\
     eval_operand (Var out) sCopy = SOME a /\ copy_old_operand saCopy (Var out) /\
     op_taint tnCopy (Var out) = {} /\
     w2n a = w2n bw + (case bd of Fixed _ => 0 | Dynamic _ => 32) + k * stride /\
     w2n dw + stride <= sCopy.vs_alloca_next /\
     (c.ce_is_ctor ==>
       op_prov GCopy (Var out) = NONE /\ w2n a + stride <= lo /\ lo <= w2n dw /\
       w2n a + stride <= sCopy.vs_alloca_next /\
       loweringStateRelDefs$regions_disjoint (w2n a) stride (w2n dw) stride /\
       !region. c.ce_imm_alloca = SOME region ==>
         eval_operand region sCopy = SOME 0w /\ copy_old_operand saCopy region /\
         op_taint tnCopy region = {} /\ op_prov GCopy region = NONE) /\
     (~c.ce_is_ctor ==>
       w2n a + stride <= LENGTH sCopy.vs_data_section /\ w2n a + stride < dimword (:256))`
    >- (drule_then strip_assume_tac body_inv_main_code >>
     `expr_sim_inv_mods [(NONE,tops)] c cx env es` by
       fs[exprSimHypsDefsTheory.expr_sim_inv_split_def] >>
     irule (INST_TYPE [alpha |-> ``:256``] for_immutable_element_copy_input_mods) >>
     simp[elem_size_in_location_def,is_slot_addressed_def] >> rpt conj_tac
     >- (qexists_tac `aidItem` >> simp[])
     >- (qexistsl [`av`,`bindings`,`e`,`env`,`id`,`loop_body`,
                    `[(NONE,tops)]`,`bound`,`Value (ArrayV av)`] >>
         simp[main_module_def, ALOOKUP_def])
     >- (qexistsl [`H`,`ctx`,`func`] >> simp[])
     >> qexistsl [`D`,`d`] >> simp[]) >>
  suspend "immutable_binding"
QED

Resume for_nonslot_array_element_prepare_full[immutable_binding]:
  qpat_x_assum `expr_type e = ArrayT fty bd /\ _`
    (fn th =>
      let val facts = CONJUNCTS th in
        map_every assume_tac (List.take (facts, List.length facts - 1)) >>
        qx_choose_then `v` (qx_choose_then `a`
          (map_every assume_tac o CONJUNCTS)) (List.last facts)
      end) >>
  qabbrev_tac `entry = <|assignable := F; type := dtv; value := v; popped := []|>` >>
  qabbrev_tac `ee = es with scopes updated_by CONS (FEMPTY |+ (id,entry))` >>
  `ee.scopes = (FEMPTY |+ (id,entry)) :: es.scopes` by simp[Abbr`ee`] >>
  `push_scope_with_var id dtv v es = (INL (),ee)` by
    simp[Abbr`ee`, Abbr`entry`, vyperStateTheory.push_scope_with_var_def,
         vyperStateTheory.return_def] >>
  `read_result cx (EL k vs) es = (INL v,es)` by
    simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  suspend "immutable_copy_antecedents"
QED

Resume for_nonslot_array_element_prepare_full[immutable_copy_antecedents]:
  `venomMemDefs$allocas_non_overlapping sCopy` by
    (qpat_assum `stmt_state_rel H ctx func c cx es sCopy`
       (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     simp[venomMemDefsTheory.alloca_inv_def]) >>
  `bc.ce_imm_alloca = c.ce_imm_alloca` by
    (drule bodySimTheory.cenv_top_ext_same_frame >>
     simp[bodySimTheory.same_frame_def] >> strip_tac >>
     qpat_x_assum `_ = c` (SUBST1_TAC o SYM) >> simp[]) >>
  `!name reg sz. FLOOKUP bc.ce_vars name = SOME (PtrVar (Var reg) sz) ==>
      not_fresh_at saCopy reg` by
    (rpt gen_tac >> disch_tac >> Cases_on `name = id`
     >- (qpat_x_assum `FLOOKUP bc.ce_vars name = SOME _` mp_tac >>
         simp[] >> disch_then (SUBST1_TAC o SYM o CONJUNCT1) >> simp[]) >>
     `FLOOKUP c.ce_vars name = SOME (PtrVar (Var reg) sz)` by
       (qpat_assum `!nm. nm <> id ==> FLOOKUP bc.ce_vars nm = FLOOKUP c.ce_vars nm`
          (qspec_then `name` mp_tac) >> simp[] >>
        disch_then (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     qpat_assum `local_ptrs_reserved c saCopy`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     qpat_assum `!n1 n2 x sz1 sz2. FLOOKUP c.ce_vars n1 = _ ==> _`
       (qspecl_then [`name`,`name`,`reg`,`sz`,`sz`] mp_tac) >> simp[]) >>
  `local_ptrs_reserved bc saCopy` by
    (qpat_assum `local_ptrs_reserved bc sbCopy`
       (mp_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     simp[local_ptrs_reserved_def] >> strip_tac >> rpt conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!name reg sz. FLOOKUP bc.ce_vars name = _ ==> not_fresh_at saCopy reg`
           irule >> goal_assum (drule_at Any)) >>
     rpt strip_tac >> simp[] >> irule local_ptrs_reserved_imm_base >>
     qexists_tac `c` >> simp[]) >>
  `!name. IS_SOME (lookup_scopes name es.scopes) ==>
      FLOOKUP bc.ce_vars name = FLOOKUP c.ce_vars name` by
    (gen_tac >> Cases_on `name = id` >> simp[]) >>
  `!name base size. local_region c es.scopes sCopy name base size <=>
      local_region c es.scopes s name base size` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  `alloca_frame c es0 sa0 s0 c es sCopy` by
    (irule stmtSimDefsTheory.alloca_frame_trans >> qexistsl [`c`,`es`,`s`,`sa0`] >>
     simp[] >> simp[stmtSimDefsTheory.alloca_frame_def] >> rpt strip_tac >>
     first_x_assum irule >> goal_assum (drule_at Any)) >>
  (* Anchor the copy wrapper on the live scopes. Its result composes with
     the original frame, without imposing source-name agreement on es0. *)
  `alloca_frame c es sa0 sCopy bc (es with scopes := FEMPTY :: es.scopes) sCopy` by
    (simp[stmtSimDefsTheory.alloca_frame_def] >> rpt strip_tac >>
     first_x_assum irule >> qexists_tac `n` >>
     qpat_x_assum `local_region bc _ sCopy n b sz'` mp_tac >>
     simp[local_region_def, vyperStateTheory.lookup_scopes_def, FLOOKUP_EMPTY] >>
     disch_then (qx_choose_then `en` (qx_choose_then `reg`
       (qx_choose_then `w` strip_assume_tac))) >>
     `IS_SOME (lookup_scopes n es.scopes)` by simp[] >>
     qpat_assum `!name. IS_SOME (lookup_scopes name es.scopes) ==> _`
       (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
     `not_fresh_at sa reg` by
       (qpat_assum `local_ptrs_reserved c sa`
          (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
        qpat_assum `!n1 n2 x sz1 sz2. FLOOKUP c.ce_vars n1 = _ ==> _`
          (qspecl_then [`n`,`n`,`reg`,`sz'`,`sz'`] mp_tac) >> simp[]) >>
     qexists_tac `reg` >> simp[] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x sCopy = lookup_var x s`
       (qspec_then `reg` mp_tac) >> simp[]) >>
  suspend "immutable_copy_size"
QED

Resume for_nonslot_array_element_prepare_full[immutable_copy_size]:
  `compile_iter_elem_copy c (Var out) (Var xd) stride LocCode F fty fty
     saCopy = ((),sbCopy)` by
    (qpat_assum `compile_iter_elem_copy c addr (Var xd) stride loc
       (is_slot_addressed loc) fty sty saCopy = ((),sbCopy)` mp_tac >>
     qpat_assum `loc = LocCode` (fn th => REWRITE_TAC [th]) >>
     qpat_assum `addr = Var out` (fn th => REWRITE_TAC [th]) >>
     qpat_assum `sty = fty` (fn th => REWRITE_TAC [th]) >>
     simp[is_slot_addressed_def, NoAsms]) >>
  `allocas_from lo sCopy /\ (ctx_has_dalloca ctx ==> allocas_below_fmp sCopy)` by
    (`allocas_from lo sCopy = allocas_from lo s /\
       allocas_below_fmp sCopy = allocas_below_fmp s` by
       (REWRITE_TAC[allocas_from_def, allocas_below_fmp_def] >>
        qpat_assum `sCopy.vs_allocas = s.vs_allocas` SUBST1_TAC >>
        qpat_assum `sCopy.vs_initial_fmp = s.vs_initial_fmp` SUBST1_TAC >>
        qpat_assum `sCopy.vs_fmp = s.vs_fmp` SUBST1_TAC >> simp[NoAsms]) >> simp[]) >>
  `!region. c.ce_is_ctor /\ c.ce_imm_alloca = SOME region ==>
    eval_operand region sCopy = SOME 0w /\ copy_old_operand saCopy region /\
    op_taint tnCopy region = {} /\ op_prov GCopy region = NONE` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `c.ce_is_ctor ==> _ /\ _ /\ _ /\ _ /\
                      loweringStateRelDefs$regions_disjoint _ _ _ _ /\ _`
       (drule_then (qspec_then `region` mp_tac o List.last o CONJUNCTS)) >> simp[]) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
  `?n Gf tnf z.
     32*n = stride /\
     compile_imm_copy_to_memory c.ce_is_ctor c.ce_imm_alloca
       (Var out) (Var xd) n 0 saCopy = ((),sbCopy) /\
     copy_runtime_frame saCopy sCopy sbCopy z /\
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sCopy,GCopy,tnCopy) []
       (OK (z with vs_inst_idx := LENGTH sbCopy.cs_current_insts),Gf,tnf)) /\
     z.vs_current_bb = sbCopy.cs_current_bb /\ ~z.vs_halted /\
     val_in_memory dtv v (w2n dw) z.vs_memory /\ val_footprint dtv v <= stride /\
     LENGTH sCopy.vs_memory <= LENGTH z.vs_memory /\
     (!off len. off+len <= w2n dw \/ w2n dw+stride <= off ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len sCopy.vs_memory) /\
     (z with <|vs_vars := sCopy.vs_vars; vs_memory := sCopy.vs_memory|>) = sCopy /\
     alloca_frame c es sa0 sCopy bc ee z /\
     (!i. i IN tnf.t_mem <=>
       if w2n dw <= i /\ i < w2n dw + stride
       then c.ce_is_ctor /\ w2n a + (i - w2n dw) IN tnCopy.t_mem
       else i IN tnCopy.t_mem) /\
     tnf.t_stor = tnCopy.t_stor /\ tnf.t_trans = tnCopy.t_trans /\
     tnf.t_imm = tnCopy.t_imm /\
     (!x. not_fresh_at saCopy x ==> FLOOKUP Gf x = FLOOKUP GCopy x /\
       op_taint tnf (Var x) = op_taint tnCopy (Var x)) /\
     allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
     (!p sz. not_fresh_at saCopy p /\ ptr_covers GCopy tnCopy p sCopy sz ==>
       ptr_covers Gf tnf p z sz)`
  >- (qpat_x_assum `stride = 32 \/ ?q. stride = 32 * q /\ 32 < stride`
       (DISJ_CASES_THEN2 ASSUME_TAC (qx_choose_then `q` strip_assume_tac))
      >- suspend "immutable_word_copy"
      >> suspend "immutable_large_copy")
  >> suspend "immutable_positioned_join"
QED

Resume for_nonslot_array_element_prepare_full[immutable_word_copy]:
  `compile_iter_elem_copy c (Var out) (Var xd) 32 LocCode F fty fty
     saCopy = ((),sbCopy)` by
    (qpat_assum `stride = 32` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  drule (INST_TYPE [alpha |-> ``:256``] for_immutable_word_element_joint_frame) >>
  disch_then (fn th => qpat_assum `stmt_state_rel H ctx func c cx es sCopy`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (drule_at (Pat `immutable_holds _ _ _ (Value _) _ _ _`)) >>
  disch_then (fn th => qpat_assum `alloca_frame c es sa0 sCopy bc _ sCopy`
    (mp_then (Pat `alloca_frame _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `ptr_covers GCopy tnCopy xd sCopy capacity`
    (mp_then (Pat `ptr_covers _ _ _ _ _`) mp_tac th)) >>
  disch_then (drule_at (Pat `ee.scopes = _`)) >>
  disch_then (fn th => qpat_assum `FLOOKUP sCopy.vs_allocas aidItem = SOME _`
    (mp_then (Pat `FLOOKUP _ _ = SOME (_,_)`) mp_tac th)) >>
  disch_then (qspecl_then [`dtv`,`lo`,`explicit`,`PG`,`D`] mp_tac) >>
  (impl_tac >- (Cases_on `c.ce_is_ctor` >> fs[])) >>
  disch_then (qx_choose_then `GWord` (qx_choose_then `tnWord`
    (qx_choose_then `zWord` (map_every assume_tac o CONJUNCTS)))) >>
  `compile_imm_copy_to_memory c.ce_is_ctor c.ce_imm_alloca (Var out) (Var xd)
     (SUC 0) 0 saCopy = ((),sbCopy)` by
    (qpat_assum `compile_iter_elem_copy c (Var out) (Var xd) 32 LocCode F fty fty
       saCopy = ((),sbCopy)` mp_tac >>
     simp[whitelistForIterImmCopyTheory.immutable_iter_small_copy,
       compile_imm_copy_to_memory_def, compile_lit_byte_offset_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def, NoAsms] >>
     pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
  Cases_on `c.ce_is_ctor`
  >- suspend "immutable_word_ctor"
  >> suspend "immutable_word_runtime"
QED

(* Reuse the range witnesses for the precise one-word taint result.
   Only the raw state is identified with the semantic wrapper endpoint. *)
Resume for_nonslot_array_element_prepare_full[immutable_word_ctor]:
  fs[] >>
  drule (bodyFullUnwrapCodeCtorRunTheory.code_copy_ctor_range_origin_ptr |>
    Q.INST [`off` |-> `0`] |> SRULE []) >>
  disch_then (fn th => qpat_assum `ptr_covers GCopy tnCopy xd sCopy capacity`
    (mp_then (Pat `ptr_covers _ _ _ _ _`) mp_tac th)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var out) sCopy = SOME a`)) >>
  disch_then (drule_at (Pat `lookup_var xd sCopy = SOME dw`)) >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`,`<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> simp[])) >>
  disch_then (qx_choose_then `Gf` (qx_choose_then `tnf`
    (qx_choose_then `z` (map_every assume_tac o CONJUNCTS)))) >>
  `z = zWord` by
    (qpat_assum `copy_runtime_frame saCopy sCopy sbCopy z`
      (mp_tac o SRULE [exprSimCopyTheory.copy_runtime_frame_def]) >>
     qpat_assum `copy_runtime_frame saCopy sCopy sbCopy zWord`
      (mp_tac o SRULE [exprSimCopyTheory.copy_runtime_frame_def]) >> simp[NoAsms]) >>
  qpat_assum `z = zWord` SUBST_ALL_TAC >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sCopy,GCopy,tnCopy) []
     (OK (zWord with vs_inst_idx := LENGTH sbCopy.cs_current_insts),Gf,tnf)` by
    (gen_tac >> irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
     first_assum ACCEPT_TAC) >>
  qexistsl [`Gf`,`tnf`,`zWord`] >> simp[] >>
  qpat_assum `sCopy.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_nonslot_array_element_prepare_full[immutable_word_runtime]:
  fs[] >>
  drule (bodyFullUnwrapCodeRuntimeRunTheory.runtime_code_copy_range_origin |>
    Q.INST [`off` |-> `0`] |> SRULE []) >>
  disch_then (fn th => qpat_assum `ptr_covers GCopy tnCopy xd sCopy capacity`
    (mp_then (Pat `ptr_covers _ _ _ _ _`) mp_tac th)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var out) sCopy = SOME a`)) >>
  disch_then (drule_at (Pat `lookup_var xd sCopy = SOME dw`)) >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`,`<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >>
    simp[IgnAsm `w2n a = _`, IgnAsm `sCopy.vs_data_section = _`])) >>
  disch_then (qx_choose_then `Gf` (qx_choose_then `tnf`
    (qx_choose_then `z` (map_every assume_tac o CONJUNCTS)))) >>
  `z = zWord` by
    (qpat_assum `copy_runtime_frame saCopy sCopy sbCopy z`
      (mp_tac o SRULE [exprSimCopyTheory.copy_runtime_frame_def]) >>
     qpat_assum `copy_runtime_frame saCopy sCopy sbCopy zWord`
      (mp_tac o SRULE [exprSimCopyTheory.copy_runtime_frame_def]) >> simp[NoAsms]) >>
  qpat_assum `z = zWord` SUBST_ALL_TAC >>
  `!i. i IN tnf.t_mem <=>
     if w2n dw <= i /\ i < w2n dw + 32 then F else i IN tnCopy.t_mem` by
    (qpat_assum `tnf.t_mem = _` SUBST1_TAC >>
     simp[pred_setTheory.IN_DIFF, CONJ_COMM, NoAsms]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sCopy,GCopy,tnCopy) []
     (OK (zWord with vs_inst_idx := LENGTH sbCopy.cs_current_insts),Gf,tnf)` by
    (gen_tac >> irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
     first_assum ACCEPT_TAC) >>
  qexistsl [`Gf`,`tnf`,`zWord`] >> simp[IgnAsm `tnf.t_mem = _`] >>
  qpat_assum `sCopy.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_nonslot_array_element_prepare_full[immutable_large_copy]:
  `compile_iter_elem_copy c (Var out) (Var xd) (32*q) LocCode F fty fty
     saCopy = ((),sbCopy)` by
    (qpat_assum `stride = 32*q` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_assum `compile_iter_elem_copy c (Var out) (Var xd) (32*q) LocCode F fty fty
     saCopy = ((),sbCopy)`
    (mp_then (Pat `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _`)
      mp_tac (INST_TYPE [alpha |-> ``:256``] for_immutable_large_element_joint_frame)) >>
  disch_then (fn th => qpat_assum `stmt_state_rel H ctx func c cx es sCopy`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (drule_at (Pat `immutable_holds _ _ _ (Value _) _ _ _`)) >>
  disch_then (fn th => qpat_assum `alloca_frame c es sa0 sCopy bc _ sCopy`
    (mp_then (Pat `alloca_frame _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `ptr_covers GCopy tnCopy xd sCopy capacity`
    (mp_then (Pat `ptr_covers _ _ _ _ _`) mp_tac th)) >>
  disch_then (drule_at (Pat `ee.scopes = _`)) >>
  disch_then (fn th => qpat_assum `FLOOKUP sCopy.vs_allocas aidItem = SOME _`
    (mp_then (Pat `FLOOKUP _ _ = SOME (_,_)`) mp_tac th)) >>
  disch_then (qspecl_then [`dtv`,`lo`,`explicit`,`PG`,`<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`] mp_tac) >>
  (impl_tac >- (Cases_on `c.ce_is_ctor` >> fs[] >> metis_tac[])) >>
  disch_then (qx_choose_then `Gf` (qx_choose_then `tnf`
    (qx_choose_then `z` (map_every assume_tac o CONJUNCTS)))) >>
  `compile_imm_copy_to_memory c.ce_is_ctor c.ce_imm_alloca (Var out) (Var xd)
      q 0 saCopy = ((),sbCopy)` by
    (`32 < 32*q` by metis_tac[] >>
     `(32*q+31) DIV 32 = q` by simp[Once MULT_COMM, ADD_DIV_ADD_DIV] >>
     drule whitelistForIterImmCopyTheory.immutable_iter_large_copy >> simp[] >>
     disch_then (fn th => fs[th])) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sCopy,GCopy,tnCopy) []
     (OK (z with vs_inst_idx := LENGTH sbCopy.cs_current_insts),Gf,tnf)` by
    (gen_tac >> irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
     first_assum ACCEPT_TAC) >>
  qexistsl [`q`,`Gf`,`tnf`,`z`] >>
  qpat_assum `stride = 32*q` SUBST1_TAC >>
  conj_tac >- REFL_TAC >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_nonslot_array_element_prepare_full[immutable_positioned_join]:
  qpat_x_assum `?n Gf tnf z. 32*n = stride /\ _`
    (qx_choose_then `n` (qx_choose_then `Gf` (qx_choose_then `tnf`
      (qx_choose_then `z` (map_every assume_tac o CONJUNCTS))))) >>
  qabbrev_tac `t = z with vs_inst_idx := LENGTH sbCopy.cs_current_insts` >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory dtv v (w2n dw) mem`
  >- (reverse (Cases_on `c.ce_is_ctor`)
      >- (simp[Abbr`t`, NoAsms] >> rpt strip_tac >>
          irule exprSimPropsTheory.val_in_memory_footprint_agree >>
          conj_tac >- (qpat_assum `stv = dtv` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
          qexists_tac `z.vs_memory` >>
          reverse conj_tac >- first_assum ACCEPT_TAC >>
          irule logStoreDataOriginPtrTheory.mem_agree_outside_window >>
          qexists_tac `tnf.t_mem` >>
          reverse conj_tac >- first_assum ACCEPT_TAC >>
          qx_gen_tac `i` >> disch_tac >>
          `w2n dw <= i /\ i < w2n dw + stride` by decide_tac >>
          qpat_assum `!i. i IN tnf.t_mem <=> _` (qspec_then `i` SUBST1_TAC) >>
          simp[]) >>
      suspend "immutable_robust_ctor") >>
  suspend "immutable_frame_join"
QED

Resume for_nonslot_array_element_prepare_full[immutable_robust_ctor]:
  `compile_imm_copy_to_memory T c.ce_imm_alloca (Var out) (Var xd) n 0
     saCopy = ((),sbCopy)` by
    (qpat_assum `compile_imm_copy_to_memory c.ce_is_ctor _ _ _ n 0 _ = _` mp_tac >>
     qpat_assum `c.ce_is_ctor` (fn th => simp[th,NoAsms])) >>
  `copy_old_operand saCopy (Var xd) /\ eval_operand (Var xd) sCopy = SOME dw` by
    simp[exprSimCopyTheory.copy_old_operand_def,eval_operand_def] >>
  drule exprSimCopyTheory.copy_ctor_run >>
  disch_then (drule_at (Pat `eval_operand (Var out) sCopy = SOME a`)) >>
  disch_then (drule_at (Pat `eval_operand (Var xd) sCopy = SOME dw`)) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `rawCopy` strip_assume_tac) >>
  `rawCopy = z` by
    (qpat_assum `copy_runtime_frame saCopy sCopy sbCopy rawCopy`
      (mp_tac o SRULE [exprSimCopyTheory.copy_runtime_frame_def]) >>
     qpat_assum `copy_runtime_frame saCopy sCopy sbCopy z`
      (mp_tac o SRULE [exprSimCopyTheory.copy_runtime_frame_def]) >> simp[NoAsms]) >>
  qpat_x_assum `rawCopy = z` SUBST_ALL_TAC >>
  `stride = type_memory_size dtv` by metis_tac[] >>
  `n = type_slot_size dtv` by
    (mp_tac (Q.SPEC `dtv` (CONJUNCT1 valueEncodingPropsTheory.type_memory_size_slots)) >>
     qpat_assum `32*n = stride` mp_tac >>
     qpat_assum `stride = type_memory_size dtv` mp_tac >> decide_tac) >>
  qpat_assum `c.ce_is_ctor ==> op_prov GCopy (Var out) = NONE /\ _`
    (fn th => qpat_assum `c.ce_is_ctor` (map_every assume_tac o CONJUNCTS o MP th)) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `mem_bytes_at (w2n dw) stride z.vs_memory =
       mem_bytes_at (w2n a) stride sCopy.vs_memory`
  >- (`w2n a + stride < dimword(:256) /\ w2n dw + stride < dimword(:256)` by
        (qpat_assum `w2n dw + capacity < dimword(:256)` mp_tac >>
         qpat_assum `w2n a + stride <= lo` mp_tac >>
         qpat_assum `lo <= w2n dw` mp_tac >> decide_tac) >>
      `type_slot_size dtv <> 0` by
        (qpat_assum `stride = 32 \/ ?q. _` mp_tac >>
         qpat_assum `32*n = stride` mp_tac >> simp[]) >>
      qpat_assum `z.vs_memory = _` SUBST1_TAC >>
      qpat_assum `n = type_slot_size dtv` SUBST1_TAC >>
      `w2n a + type_memory_size dtv < dimword(:256) /\
       w2n dw + type_memory_size dtv < dimword(:256) /\
       regions_disjoint (w2n a) (type_memory_size dtv) (w2n dw) (type_memory_size dtv)` by
        (qpat_assum `stride = type_memory_size dtv` (SUBST1_TAC o SYM) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      drule_all exprSimCopyTheory.copy_ctor_memory_snapshot >>
      disch_then (qspec_then `sCopy` SUBST1_TAC) >>
      qpat_assum `stride = type_memory_size dtv` (SUBST1_TAC o SYM) >>
      REWRITE_TAC[immutableConstructorRelationTheory.immutable_copy_memory_readback]) >>
  suspend "immutable_robust_ctor_source"
QED

Resume for_nonslot_array_element_prepare_full[immutable_robust_ctor_source]:
  qpat_assum `immutable_holds c cx fty (Value v) a es sCopy`
    (mp_tac o REWRITE_RULE [loweringPostsTheory.immutable_holds_def]) >>
  disch_then (qx_choosel_then [`root`,`ro`,`rt`,`rvRoot`,`ra`,`ctv`,`cv`]
    (map_every assume_tac o CONJUNCTS)) >>
  `ctv = dtv` by
    (qpat_assum `evaluate_type (get_tenv cx) fty = SOME ctv` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) fty = SOME dtv`
       (fn th => simp[th,NoAsms])) >>
  `cv = v` by
    (qpat_assum `read_result cx (Value v) es = (INL cv,es)` mp_tac >>
     simp[vyperStateTheory.read_result_def,vyperStateTheory.return_def,NoAsms]) >>
  drule_then strip_assume_tac body_inv_main_code >>
  `c.ce_module = NONE` by metis_tac[body_inv_module_locations] >>
  `get_tenv cx = type_env tops` by
    (drule_then assume_tac bodySimTheory.body_inv_contract >>
     drule_then assume_tac contract_inv_type_env >>
     fs[vyperContextTheory.type_env_all_modules_def, vyperContextTheory.type_env_def]) >>
  `immutable_value_admissible rt rvRoot /\ val_in_memory rt rvRoot ro sCopy.vs_memory` by
    (qpat_assum `stmt_state_rel H ctx func c cx es sCopy`
       (mp_tac o MATCH_MP stateRelProjTheory.state_rel_immutables_rel o
        MATCH_MP stateRelProjTheory.stmt_state_rel_state_rel) >>
     simp[immutables_rel_def,NoAsms] >>
     disch_then (qspecl_then [`root`,`rt`,`rvRoot`,`ro`] mp_tac) >> simp[]) >>
  drule bodySimTheory.body_inv_immutable_section_layout >>
  simp[immutableRelationTheory.immutable_section_layout_def,NoAsms] >>
  disch_then (qspecl_then [`root`,`ro`] mp_tac) >>
  (impl_tac >-
     (qpat_assum `FLOOKUP c.ce_module_vars (c.ce_module,root) = SOME (ImmutableLoc ro)` mp_tac >>
      qpat_assum `c.ce_module = NONE` SUBST1_TAC >> simp[NoAsms])) >>
  disch_then (qx_choosel_then [`pre`,`post`,`vis`,`rty`,`slot`] strip_assume_tac) >>
  `env_context_consistent env cx /\ env_immutables_consistent env cx es` by
    (qpat_assum `expr_sim_inv c cx env es` mp_tac >>
     simp[exprSimHypsDefsTheory.expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
          NoAsms]) >>
  `FLOOKUP env.bare_globals (NONE,root) = SOME rty` by
    (`MEM (VariableDecl vis Immutable root rty slot) tops` by
       (qpat_assum `tops = _` SUBST1_TAC >> simp[]) >>
     qpat_assum `env_context_consistent env cx` mp_tac >>
     simp[vyperTypeInvariantsTheory.env_context_consistent_def,
          vyperTypeInvariantsTheory.bare_globals_complete_def, NoAsms] >>
     strip_tac >>
     qpat_assum `!src ts vis mut id ty init. _ ==> FLOOKUP env.bare_globals (src,id) = SOME ty`
       (qspecl_then [`NONE`,`tops`,`vis`,`Immutable`,`root`,`rty`,`slot`] mp_tac) >>
     simp[]) >>
  `evaluate_type (type_env tops) rty = SOME rt` by
    (`FLOOKUP (get_source_immutables NONE
        (case ALOOKUP es.immutables cx.txn.target of SOME m => m | NONE => [])) root =
        SOME (rt,rvRoot)` by
       (qpat_assum `FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY | SOME imms => _) root = SOME (rt,rvRoot)` mp_tac >>
        qpat_assum `c.ce_module = NONE` SUBST1_TAC >>
        Cases_on `ALOOKUP es.immutables cx.txn.target` >>
        simp[vyperStateTheory.get_source_immutables_def,NoAsms]) >>
     qpat_assum `env_immutables_consistent env cx es`
       (mp_tac o cj 2 o SRULE [vyperTypeInvariantsTheory.env_immutables_consistent_def]) >>
     disch_then drule_all >> simp[]) >>
  suspend "immutable_robust_ctor_decl"
QED

Resume for_nonslot_array_element_prepare_full[immutable_robust_ctor_decl]:
  `ra + stride <= type_memory_size rt` by
    (qpat_assum `sub_layout rt rvRoot ra ctv cv`
       (mp_tac o cj 1 o REWRITE_RULE [loweringPostsTheory.sub_layout_def]) >>
     simp[]) >>
  `ro + ra < dimword(:256)` by
    (qpat_assum `ro + type_memory_size rt < dimword(:256)` mp_tac >>
     qpat_assum `ra + stride <= type_memory_size rt` mp_tac >> decide_tac) >>
  `w2n a = ro + ra` by
    (qpat_assum `a = n2w (ro + ra)` (fn th => REWRITE_TAC[th,w2n_n2w]) >>
     irule LESS_MOD >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `nn = MAX lo (ro + type_memory_size rt)` >>
  qabbrev_tac `padded = mem_bytes_at 0 nn sCopy.vs_memory` >>
  `LENGTH padded = nn` by simp[Abbr`padded`,valueEncodingPropsTheory.LENGTH_mem_bytes_at] >>
  `lo <= nn /\ ro + type_memory_size rt <= nn` by simp[Abbr`nn`,MAX_DEF] >>
  `mem_bytes_at ro (type_memory_size rt) padded =
   mem_bytes_at ro (type_memory_size rt) sCopy.vs_memory` by
    (`ro + type_memory_size rt <= LENGTH padded` by
       (qpat_assum `LENGTH padded = nn` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     pop_assum (SUBST1_TAC o MATCH_MP valueEncodingDefsTheory.mem_bytes_at_bounded) >>
     simp[Abbr`padded`,NoAsms] >>
     mp_tac (Q.SPECL [`0`,`ro`,`type_memory_size rt`,`nn`,`sCopy.vs_memory`]
       abiCanonicalHeadSizeTheory.mem_bytes_at_window) >>
     disch_then (fn th => qpat_assum `ro + type_memory_size rt <= nn`
       (ACCEPT_TAC o REWRITE_RULE [ADD_CLAUSES] o MP th))) >>
  `val_in_memory rt rvRoot ro padded` by
    (match_mp_tac valueEncodingPropsTheory.val_in_memory_mem_agree >>
     qexistsl_tac [`type_memory_size rt`,`sCopy.vs_memory`] >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (irule (cj 1 loweringSliceTheory.immutable_admissible_val_wf) >>
         first_assum ACCEPT_TAC)
     >- simp[NoAsms] >>
     sym_tac >> first_assum ACCEPT_TAC) >>
  suspend "immutable_robust_ctor_padded"
QED

Resume for_nonslot_array_element_prepare_full[immutable_robust_ctor_padded]:
  `c.ce_struct_fields = make_struct_fields_map tops` by
    (drule_then assume_tac bodySimTheory.body_inv_contract >>
     drule_then assume_tac contract_inv_struct_fields >>
     fs[compileUnitTheory.make_struct_fields_map_mods_singleton]) >>
  `!ty tv. evaluate_type (type_env tops) ty = SOME tv ==>
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty = type_memory_size tv` by
    (qpat_assum `c.ce_struct_fields = _` (SUBST1_TAC o SYM) >>
     qpat_assum `get_tenv cx = type_env tops` (SUBST1_TAC o SYM) >>
     simp[structFieldsPropsTheory.type_mem_bytes_type_memory_bytes,NoAsms] >>
     rpt strip_tac >> drule_all exprSimHypsTheory.expr_sim_inv_memory_size >> simp[]) >>
  qabbrev_tac `short = mem_bytes_at 0 lo sCopy.vs_memory` >>
  `!j. j < lo /\ j IN tnCopy.t_mem ==> imm_section_dead tops short j` by
    (qpat_assum `ghost_inv_at D lo d c cx es GCopy tnCopy sCopy`
       (mp_tac o cj 5 o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     simp[Abbr`short`]) >>
  `!j. ro <= j /\ j < ro + type_memory_size rt /\ imm_section_dead tops short j ==>
       mem_dead_bytes short ro rt j` by
    (qx_gen_tac `j` >> DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
     qpat_x_assum `imm_section_dead tops short j`
       (mp_tac o REWRITE_RULE [immSectionDeadTheory.imm_section_dead_def]) >>
     disch_then (qx_choosel_then [`pre'`,`vis'`,`root'`,`rty'`,`slot'`,`post'`,`rt'`]
       (map_every assume_tac o CONJUNCTS)) >>
     qabbrev_tac `sf = get_struct_fields (make_struct_fields_map tops)` >>
     qabbrev_tac `ro' = compute_immutables_len sf pre'` >>
     drule (cj 1 ctorDeployDeadSectionTheory.mem_dead_bytes_range) >> strip_tac >>
     `type_mem_bytes sf rty = type_memory_size rt` by
       (qpat_assum `!ty tv. evaluate_type (type_env tops) ty = SOME tv ==> _`
         irule >> first_assum ACCEPT_TAC) >>
     `type_mem_bytes sf rty' = type_memory_size rt'` by
       (qpat_assum `!ty tv. evaluate_type (type_env tops) ty = SOME tv ==> _`
         irule >> first_assum ACCEPT_TAC) >>
     `pre ++ VariableDecl vis Immutable root rty slot :: post =
      pre' ++ VariableDecl vis' Immutable root' rty' slot' :: post'` by
       (qpat_assum `tops = pre ++ [VariableDecl vis Immutable root rty slot] ++ post` mp_tac >>
        qpat_assum `tops = pre' ++ VariableDecl vis' Immutable root' rty' slot' :: post'`
          (fn th => simp[th,NoAsms,EQ_SYM_EQ])) >>
     first_assum (mp_tac o MATCH_MP
       (Q.INST [`sft` |-> `sf`] ctorDeployDeadSectionFrameTheory.imm_frame_occurrence_separation)) >>
     qpat_assum `Abbrev (ro' = _)` (fn th => REWRITE_TAC[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     qpat_assum `ro = compute_immutables_len sf pre` (SUBST1_TAC o SYM) >>
     strip_tac
     >- (qpat_assum `pre = pre'` (SUBST_ALL_TAC o SYM) >>
         qpat_assum `pre ++ VariableDecl vis Immutable root rty slot :: post = _` mp_tac >>
         simp[APPEND_11,NoAsms] >> strip_tac >>
         qpat_assum `rty = rty'` (SUBST_ALL_TAC o SYM) >>
         `rt = rt'` by
           (qpat_assum `evaluate_type (type_env tops) rty = SOME rt` mp_tac >>
            qpat_assum `evaluate_type (type_env tops) rty = SOME rt'` (fn th => simp[th,NoAsms])) >>
         qpat_assum `rt = rt'` (SUBST_ALL_TAC o SYM) >>
         qpat_assum `ro = compute_immutables_len sf pre` SUBST1_TAC >>
         simp[Abbr`ro'`])
     >- (qpat_assum `ro + type_mem_bytes sf rty <= ro'` mp_tac >>
         qpat_assum `type_mem_bytes sf rty = type_memory_size rt` SUBST1_TAC >>
         qpat_assum `j < ro + type_memory_size rt` mp_tac >>
         qpat_assum `ro' <= j` mp_tac >> decide_tac) >>
     qpat_assum `ro' + type_mem_bytes sf rty' <= ro` mp_tac >>
     qpat_assum `type_mem_bytes sf rty' = type_memory_size rt'` SUBST1_TAC >>
     qpat_assum `j < ro' + type_memory_size rt'` mp_tac >>
     qpat_assum `ro <= j` mp_tac >> decide_tac) >>
  suspend "immutable_robust_ctor_restrict"
QED

Resume for_nonslot_array_element_prepare_full[immutable_robust_ctor_restrict]:
  `!j. j <= lo ==> mem_bytes_at 0 j short = mem_bytes_at 0 j padded` by
    (qx_gen_tac `j` >> disch_tac >>
     `j <= nn` by (qpat_assum `lo <= nn` mp_tac >> decide_tac) >>
     simp[Abbr`short`,Abbr`padded`,valueEncodingDefsTheory.mem_bytes_at_bounded,
          valueEncodingPropsTheory.LENGTH_mem_bytes_at,
          abiCanonicalHeadSizeTheory.mem_bytes_at_window]) >>
  `!j. w2n a <= j /\ j < w2n a + stride /\
       ~mem_dead_bytes padded ro rt j ==> j NOTIN tnCopy.t_mem` by
    (qx_gen_tac `j` >> DISCH_THEN (map_every assume_tac o CONJUNCTS) >> strip_tac >>
     `j < lo /\ ro <= j /\ j < ro + type_memory_size rt` by
       (qpat_assum `w2n a = ro + ra` mp_tac >>
        qpat_assum `ra + stride <= type_memory_size rt` mp_tac >>
        qpat_assum `w2n a + stride <= lo` mp_tac >> decide_tac) >>
     `imm_section_dead tops short j` by
       (qpat_assum `!i. i < lo /\ i IN tnCopy.t_mem ==> _` irule >> simp[]) >>
     `mem_dead_bytes short ro rt j` by
       (qpat_assum `!i. ro <= i /\ i < ro + type_memory_size rt /\ _ ==> _`
          irule >> simp[]) >>
     `mem_bytes_at 0 j short = mem_bytes_at 0 j padded` by
       (qpat_assum `!i. i <= lo ==> mem_bytes_at 0 i short = _`
          irule >> decide_tac) >>
     drule (cj 1 for_element_dead_prefix) >>
     disch_then (qspecl_then [`ro`,`rt`] mp_tac) >> simp[]) >>
  suspend "immutable_robust_ctor_live"
QED

Resume for_nonslot_array_element_prepare_full[immutable_robust_ctor_live]:
  qx_gen_tac `mem` >> disch_tac >>
  qabbrev_tac `ao = w2n a` >> qabbrev_tac `dst = w2n dw` >>
  `ao + stride <= LENGTH padded` by decide_tac >>
  `ao + stride <= nn` by decide_tac >>
  `mem_bytes_at ao stride padded = mem_bytes_at ao stride sCopy.vs_memory` by
    (qpat_assum `ao + stride <= LENGTH padded`
       (SUBST1_TAC o MATCH_MP valueEncodingDefsTheory.mem_bytes_at_bounded) >>
     simp[Abbr`padded`,NoAsms] >>
     mp_tac (Q.SPECL [`0`,`ao`,`stride`,`nn`,`sCopy.vs_memory`]
       abiCanonicalHeadSizeTheory.mem_bytes_at_window) >>
     disch_then (fn th => qpat_assum `ao + stride <= nn`
       (ACCEPT_TAC o REWRITE_RULE [ADD_CLAUSES] o MP th))) >>
  `mem_bytes_at dst stride t.vs_memory = mem_bytes_at ao stride padded` by
    (qpat_assum `mem_bytes_at ao stride padded = _` SUBST1_TAC >>
     simp[Abbr`t`,NoAsms] >> first_assum ACCEPT_TAC) >>
  `!h. h < stride /\ ~mem_dead_bytes padded ro rt (ao+h) ==>
       EL h (mem_bytes_at dst stride mem) = EL (ao+h) padded` by
    (qx_gen_tac `h` >> DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
     `(ao+h) NOTIN tnCopy.t_mem` by
       (qpat_assum `!j. ao <= j /\ j < ao + stride /\ _ ==> _` irule >> simp[]) >>
     `dst+h NOTIN tnf.t_mem` by
       (qpat_assum `!i. i IN tnf.t_mem <=> _` (qspec_then `dst+h` SUBST1_TAC) >>
        `dst <= dst+h /\ dst+h < dst+stride /\ dst+h-dst = h` by decide_tac >>
        qpat_assum `ao+h NOTIN tnCopy.t_mem` mp_tac >>
        simp[NoAsms] >>
        rpt (first_assum (fn th => CHANGED_TAC (rewrite_tac [th])))) >>
     `mem_bytes_at (dst+h) 1 t.vs_memory = mem_bytes_at (dst+h) 1 mem` by
       (qpat_assum `mem_agree_outside tnf.t_mem t.vs_memory mem`
          (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.mem_agree_outside_def]) >>
        disch_then irule >> first_assum ACCEPT_TAC) >>
     `mem_bytes_at (dst+h) 1 t.vs_memory = mem_bytes_at (ao+h) 1 padded` by
       (qpat_assum `mem_bytes_at dst stride t.vs_memory = mem_bytes_at ao stride padded`
          (mp_then Any mp_tac valueEncodingPropsTheory.mem_bytes_at_translated_window) >>
        disch_then (qspecl_then [`h`,`1`] mp_tac) >>
        qpat_assum `h < stride` mp_tac >> simp[NoAsms]) >>
     `h < LENGTH (mem_bytes_at dst stride mem)` by
       (simp[valueEncodingPropsTheory.LENGTH_mem_bytes_at,NoAsms] >>
        first_assum ACCEPT_TAC) >>
     `ao+h < LENGTH padded` by decide_tac >>
     `mem_bytes_at h 1 (mem_bytes_at dst stride mem) = mem_bytes_at (dst+h) 1 mem` by
       (`h + 1 <= LENGTH (mem_bytes_at dst stride mem)` by decide_tac >>
        qpat_assum `h + 1 <= LENGTH (mem_bytes_at dst stride mem)`
          (SUBST1_TAC o MATCH_MP valueEncodingDefsTheory.mem_bytes_at_bounded) >>
        irule abiCanonicalHeadSizeTheory.mem_bytes_at_window >> decide_tac) >>
     `[(mem_bytes_at dst stride mem)❲h❳] = [EL (ao+h) padded]` suffices_by
       simp[NoAsms] >>
     qpat_assum `h < LENGTH (mem_bytes_at dst stride mem)`
       (SUBST1_TAC o MATCH_MP abiEncoderPropsTheory.mem_bytes_at_from_EL) >>
     qpat_assum `ao+h < LENGTH padded`
       (SUBST1_TAC o MATCH_MP abiEncoderPropsTheory.mem_bytes_at_from_EL) >>
     qpat_assum `mem_bytes_at h 1 (mem_bytes_at dst stride mem) = _` SUBST1_TAC >>
     qpat_assum `mem_bytes_at (dst+h) 1 t.vs_memory = mem_bytes_at (dst+h) 1 mem`
       (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  suspend "immutable_robust_ctor_splice"
QED

Resume for_nonslot_array_element_prepare_full[immutable_robust_ctor_splice]:
  qabbrev_tac `win = mem_bytes_at dst stride mem` >>
  qabbrev_tac `spliced = TAKE ao padded ++ win ++ DROP (ao+stride) padded` >>
  `LENGTH win = stride` by simp[Abbr`win`,NoAsms,valueEncodingPropsTheory.LENGTH_mem_bytes_at] >>
  `LENGTH (TAKE ao padded) = ao` by (irule listTheory.LENGTH_TAKE >> decide_tac) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `LENGTH spliced = LENGTH padded`
  >- (simp[Abbr`spliced`,NoAsms] >>
      qpat_assum `LENGTH (TAKE ao padded) = ao` SUBST1_TAC >>
      qpat_assum `LENGTH win = stride` SUBST1_TAC >> decide_tac) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `val_in_memory rt rvRoot ro spliced`
  >- (irule ctorDeployDeadSectionRelTheory.section_evaluated_value_memory_frame >>
      qpat_assum `evaluate_type (type_env tops) rty = SOME rt` (irule_at Any) >>
      qpat_assum `LENGTH spliced = LENGTH padded` (irule_at Any) >>
      qpat_assum `val_in_memory rt rvRoot ro padded` (irule_at Any) >>
      `ro + type_memory_size rt <= LENGTH padded` by decide_tac >>
      qpat_assum `ro + type_memory_size rt <= LENGTH padded` (irule_at Any) >>
      conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >>
      qx_gen_tac `j` >> DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
      simp[Abbr`spliced`,NoAsms,listTheory.EL_APPEND_EQN] >>
      qpat_assum `LENGTH (TAKE ao padded) = ao` SUBST1_TAC >>
      qpat_assum `LENGTH win = stride` SUBST1_TAC >>
      Cases_on `j < ao`
      >- (qpat_assum `j < ao` (fn th => simp[NoAsms,th,listTheory.EL_TAKE])) >>
      qpat_assum `~(j < ao)` (fn th => simp[NoAsms,th]) >>
      `ao <= j` by decide_tac >>
      Cases_on `j < ao + stride`
      >- (`j - ao < stride /\ ao + (j - ao) = j` by decide_tac >>
          qpat_assum `j - ao < stride` (fn th => simp[NoAsms,th]) >>
          qpat_assum `!h. h < stride /\ _ ==> EL h win = _`
            (qspec_then `j-ao` mp_tac) >>
          qpat_assum `j - ao < stride` (fn lt =>
            qpat_assum `ao + (j - ao) = j` (fn eq => simp[NoAsms,lt,eq])) >>
          disch_then irule >> first_assum ACCEPT_TAC) >>
      `~(j - ao < stride)` by decide_tac >>
      `j - ao - stride + (ao + stride) = j /\ j < LENGTH padded` by decide_tac >>
      qpat_assum `~(j - ao < stride)` (fn lt =>
        qpat_assum `j - ao - stride + (ao + stride) = j` (fn eq =>
          qpat_assum `j < LENGTH padded` (fn bd => simp[NoAsms,lt,eq,bd,listTheory.EL_DROP])))) >>
  `val_in_memory dtv v ao spliced` by
    (qpat_assum `ao = ro + ra` SUBST1_TAC >>
     qpat_assum `sub_layout rt rvRoot ra ctv cv`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.sub_layout_def]) >>
     qpat_assum `ctv = dtv` SUBST1_TAC >> qpat_assum `cv = v` SUBST1_TAC >>
     rpt strip_tac >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `mem_bytes_at ao stride spliced = win` by
    (qpat_assum `LENGTH spliced = LENGTH padded` (fn th =>
       `ao + stride <= LENGTH spliced` by (rewrite_tac [th] >> decide_tac)) >>
     qpat_assum `ao + stride <= LENGTH spliced`
       (SUBST1_TAC o MATCH_MP valueEncodingDefsTheory.mem_bytes_at_bounded) >>
     qpat_assum `LENGTH (TAKE ao padded) = ao` (SUBST1_TAC o SYM) >>
     qpat_assum `Abbrev (spliced = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND] >>
     qpat_assum `LENGTH win = stride` (SUBST1_TAC o SYM) >>
     simp[listTheory.TAKE_APPEND1,NoAsms]) >>
  irule valueEncodingPropsTheory.val_in_memory_relocate >>
  qpat_assum `val_in_memory dtv v ao spliced` (irule_at Any) >>
  qexists_tac `stride` >>
  qpat_assum `stride = type_memory_size dtv` (fn th =>
    simp[NoAsms,GSYM th]) >>
  conj_tac
  >- (qpat_assum `stv = dtv` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_assum `mem_bytes_at ao stride spliced = win` SUBST1_TAC >>
  simp[NoAsms,Abbr`win`]
QED

Resume for_nonslot_array_element_prepare_full[immutable_frame_join]:
  `t.vs_allocas = sCopy.vs_allocas` by
    (qpat_assum `(z with <|vs_vars := _; vs_memory := _|>) = sCopy`
       (mp_tac o AP_TERM ``venom_state_vs_allocas``) >>
     simp[Abbr`t`,NoAsms]) >>
  `FLOOKUP t.vs_allocas aidItem = SOME (w2n dw,capacity)` by
    (qpat_assum `t.vs_allocas = sCopy.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `lookup_var xd t = SOME dw` by
    (`lookup_var xd z = lookup_var xd sCopy` by
       (qpat_assum `copy_runtime_frame saCopy sCopy sbCopy z`
          (strip_assume_tac o REWRITE_RULE [exprSimCopyTheory.copy_runtime_frame_def]) >>
        first_x_assum irule >> first_assum ACCEPT_TAC) >>
     `lookup_var xd t = lookup_var xd z` by
       simp[Abbr`t`,lookup_var_def,NoAsms] >>
     qpat_assum `lookup_var xd t = lookup_var xd z` SUBST1_TAC >> simp[]) >>
  `ptr_covers Gf tnf xd t capacity` by
    (simp[Abbr`t`,ghostPcTransportPtrTheory.ptr_covers_inst_idx,NoAsms] >>
     qpat_assum `!p sz. not_fresh_at saCopy p /\ ptr_covers GCopy tnCopy p sCopy sz ==> _`
       irule >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)` by
    (qx_gen_tac `Dx` >> qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK sCopy,GCopy,tnCopy)`
       (qspec_then `Dx` (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
     simp[Abbr`t`]) >>
  qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)` (qspec_then `D` assume_tac) >>
  `alloca_history func t` by
    (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gf,tnf)` (irule_at Any) >>
     qpat_assum `stmt_state_rel H ctx func c cx es s`
       (strip_assume_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `!(HH:(bool # bytes32 # type_value) list # num list). stmt_state_rel HH ctx func c cx es s ==> stmt_state_rel HH ctx func bc cx ee t`
  >- suspend "immutable_bound_rel" >>

  `stmt_state_rel H ctx func bc cx ee t` by
    (qpat_assum `!(HH:(bool # bytes32 # type_value) list # num list). stmt_state_rel HH ctx func c cx es s ==> stmt_state_rel HH ctx func bc cx ee t`
       irule >> first_assum ACCEPT_TAC) >>  suspend "immutable_frame_fields"
QED

Resume for_nonslot_array_element_prepare_full[immutable_bound_rel]:
  qabbrev_tac `empty = es with scopes := FEMPTY :: es.scopes` >>
  `!(HH:(bool # bytes32 # type_value) list # num list). stmt_state_rel HH ctx func c cx es s ==>
      stmt_state_rel HH ctx func bc cx empty sCopy` by
    (gen_tac >> disch_tac >> simp[Abbr `empty`,NoAsms] >>
     irule array_empty_scope_rel_transport >> qexists_tac `c` >>
     simp[] >>
     qpat_assum `!(HH:(bool # bytes32 # type_value) list # num list). stmt_state_rel HH ctx func c cx es s ==> stmt_state_rel HH ctx func c cx es sCopy`
       irule >> first_assum ACCEPT_TAC) >>
  `not_local_ptr bc (FEMPTY::es.scopes) xd` by
    (qpat_assum `local_ptrs_reserved bc saCopy`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     simp[not_local_ptr_def, Abbr `empty`, vyperStateTheory.lookup_scopes_def] >>
     conj_tac
     >- (rpt strip_tac >>
         `name = id` by metis_tac[] >> fs[]) >>
     strip_tac >> metis_tac[]) >>
  `ee = empty with scopes := (FEMPTY |+ (id,entry)) :: es.scopes` by
    simp[Abbr `ee`, Abbr `empty`,NoAsms, vyperStateTheory.evaluation_state_component_equality] >>
  qpat_assum `ee = _` SUBST1_TAC >>
  qpat_assum `Abbrev (entry = _)`
    (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `?inst. MEM inst (fn_insts func) /\ _`
    (qx_choose_then `itemInst` (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `copy_runtime_frame saCopy sCopy sbCopy z`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [exprSimCopyTheory.copy_runtime_frame_def]) >>
  `copy_static t = copy_static sCopy` by
    (`copy_static t = copy_static z` by
       simp[Abbr `t`, exprSimStorageCopyTheory.copy_static_def, NoAsms] >>
     simp[]) >>
  qx_gen_tac `HH` >> disch_tac >>
  `stmt_state_rel HH ctx func bc cx empty sCopy` by
    (qpat_assum `!(HH:(bool # bytes32 # type_value) list # num list). stmt_state_rel HH ctx func c cx es s ==> stmt_state_rel HH ctx func bc cx empty sCopy`
       irule >> first_assum ACCEPT_TAC) >>
  irule stmtSimDeclCopyFrameTheory.stmt_state_rel_declare_copy_frame >>
  `val_wf dtv v /\ value_has_type dtv v` by
    (qpat_assum `stv = dtv` (SUBST1_TAC o SYM) >> simp[]) >>
  simp[Abbr `empty`, vyperStateTheory.lookup_scopes_def] >>
  qexistsl [`itemInst`,`sCopy`,`saCopy`,`dw`] >>
  simp[Abbr `t`, IgnAsm `sCopy = _ with vs_vars := _`] >>
  conj_tac
  >- (rpt strip_tac >> qpat_assum `!x. not_fresh_at saCopy x ==> lookup_var x z = _`
        drule >> simp[lookup_var_def,NoAsms]) >>
  rpt strip_tac >>
  qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _`
    (qspecl_then [`b`,`n'`] mp_tac) >> simp[] >> (metis_tac[])
QED

Resume for_nonslot_array_element_prepare_full[immutable_frame_fields]:
  qpat_assum `copy_runtime_frame saCopy sCopy sbCopy z`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [exprSimCopyTheory.copy_runtime_frame_def]) >>
  `sa.cs_next_var <= saCopy.cs_next_var` by
    (qpat_assum `emit_op MUL _ sa = _`
       (strip_assume_tac o MATCH_MP exprSimAccountsTheory.emit_op_extends_next_var) >>
     qpat_assum `emit_op ADD _ sn = (_,saCopy)`
       (strip_assume_tac o MATCH_MP exprSimAccountsTheory.emit_op_extends_next_var) >>
     `sm.cs_next_var <= sn.cs_next_var` suffices_by decide_tac >>
     qpat_assum `(if dyn then emit_op ADD [Lit 32w;offOp] sm = _ else _)` mp_tac >>
     Cases_on `dyn` >> simp[NoAsms] >>
     metis_tac[exprSimAccountsTheory.emit_op_extends_next_var]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at saCopy x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     `lookup_var x t = lookup_var x z` by simp[NoAsms,Abbr `t`,lookup_var_def] >>
     simp[]) >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `(z with <|vs_vars := _; vs_memory := _|>) = sCopy`
       (mp_tac o AP_TERM ``venom_state_vs_alloca_next``) >>
     simp[Abbr `t`, IgnAsm `sCopy = _ with vs_vars := _`]) >>
  `return_buf_frame d bc sbCopy t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl [`c`,`s`,`sa`] >>
     drule stmtFragPtrTheory.cenv_top_ext_return_buf >> simp[] >>
     rpt strip_tac >> decide_tac) >>
  `!x sz. bc.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            op_taint tnf (Var x) = {}` by
    (rpt strip_tac >>
     `c.ce_return_pc = SOME (PtrVar (Var x) sz)` by
       (drule stmtSimPropsTheory.cenv_top_ext_return_pc >> simp[]) >>
     `not_fresh_at saCopy x` by
       (qpat_assum `!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> _`
          (qspecl_then [`x`,`sz`] mp_tac) >> simp[]) >>
     qpat_assum `!p. not_fresh_at saCopy p ==> FLOOKUP Gf p = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[] >>
     qpat_assum `ghost_inv_at D lo d c cx es GCopy tnCopy sCopy`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     qpat_assum `!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> op_taint tnCopy (Var x) = {}`
       (qspecl_then [`x`,`sz`] mp_tac) >> simp[]) >>
  `value_has_type dtv v /\ val_wf dtv v` by
    (qpat_assum `stv = dtv` (SUBST1_TAC o SYM) >> simp[]) >>
  `ee = es with scopes := ee.scopes` by
    simp[Abbr `ee`, vyperStateTheory.evaluation_state_component_equality] >>
  `!(HH:(bool # bytes32 # type_value) list # num list). storage_well_formed_on cx es (FST HH) ==> storage_well_formed_on cx ee (FST HH)` by
    (qx_gen_tac `HH` >> disch_tac >>
     qpat_assum `ee = es with scopes := _` (fn th => simp[Once th, NoAsms,
       vyperStorageFootprintTheory.storage_well_formed_on_def,
       vyperStorageBackendTheory.get_storage_scopes]) >>
     qpat_assum `storage_well_formed_on cx es (FST HH)`
       (ACCEPT_TAC o REWRITE_RULE [vyperStorageFootprintTheory.storage_well_formed_on_def])) >>
  `alloca_frame c es0 sa0 s0 bc ee t` by
    (irule stmtSimDefsTheory.alloca_frame_same_state >> qexists_tac `z` >>
     simp[Abbr `t`, NoAsms] >>
     irule stmtSimDefsTheory.alloca_frame_trans >>
     qexistsl [`c`,`es`,`sCopy`,`sa0`] >> simp[]) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id ==>
     off + sz <= w2n dw \/ w2n dw + capacity <= off` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP sCopy.vs_allocas aid = SOME (off,sz)` by simp[] >>
     `aid <> aidItem` by decide_tac >>
     qpat_assum `allocas_non_overlapping sCopy`
       (mp_tac o REWRITE_RULE [venomMemDefsTheory.allocas_non_overlapping_def]) >>
     disch_then (qspecl_then [`aid`,`aidItem`,`off`,`sz`,`w2n dw`,`capacity`] mp_tac) >> simp[]) >>
  `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
     aid < sa0.cs_next_id /\
     (!name b len. local_region c es0.scopes s0 name b len ==>
       off + sz <= b \/ b + len <= off) /\
     off <= i /\ i < off + sz /\ i IN tnf.t_mem ==> i IN tn0.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `off + sz <= w2n dw \/ w2n dw + capacity <= off` by
       (qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
          (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[]) >>
     `~(w2n dw <= i /\ i < w2n dw + stride)` by decide_tac >>
     `i IN tn.t_mem` by
       (qpat_assum `!i. i IN tnf.t_mem <=> _` (qspec_then `i` mp_tac) >> simp[]) >>
     qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> i IN tn0.t_mem`
       (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >> simp[] >>
     disch_then irule >> first_assum ACCEPT_TAC) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC) `ghost_inv_at D lo d bc cx ee Gf tnf t`
  >- suspend "immutable_ghost" >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[]) >>
  `typed_copy_frame (w2n dw) capacity s.vs_memory t.vs_memory` by
    (`capacity = stride` by metis_tac[] >>
     qpat_assum `capacity = stride` SUBST1_TAC >>
     qpat_assum `sCopy.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
     simp[typed_copy_frame_def, Abbr `t`, NoAsms] >>
     conj_tac >-
       (qx_gen_tac `offset` >> qx_gen_tac `length` >> disch_tac >>
        qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _`
          (qspecl_then [`offset`,`length`] MATCH_MP_TAC) >> decide_tac) >>
     first_assum ACCEPT_TAC) >>
  `!i. ~(w2n dw <= i /\ i < w2n dw + capacity) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >>
     `~(w2n dw <= i /\ i < w2n dw + stride)` by decide_tac >>
     qpat_assum `!i. i IN tnf.t_mem <=> _` (qspec_then `i` SUBST1_TAC) >> simp[]) >>
  `copy_static t = copy_static s` by
    (`copy_static t = copy_static z` by
       simp[Abbr `t`, exprSimStorageCopyTheory.copy_static_def, NoAsms] >>
     qpat_assum `copy_static t = copy_static z` SUBST1_TAC >>
     qpat_assum `copy_static z = copy_static sCopy` SUBST1_TAC >>
     qpat_assum `sCopy = _ with <|vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|>`
       (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[exprSimStorageCopyTheory.copy_static_def, NoAsms]) >>
  `!HH. valid_horizon cx st0 HH es.storage_trace ==>
     stmt_state_rel HH ctx func bc cx ee t /\ storage_well_formed_on cx ee (FST HH) /\
     ghost_inv_at (DF HH) lo d bc cx ee Gf tnf t` by
    (qx_gen_tac `HH` >> disch_tac >>
     qpat_assum `!HH. valid_horizon cx st0 HH es.storage_trace ==> _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     conj_tac >-
       (qpat_assum `!(HH:(bool # bytes32 # type_value) list # num list). stmt_state_rel HH ctx func c cx es s ==> stmt_state_rel HH ctx func bc cx ee t`
          irule >> first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qpat_assum `!(HH:(bool # bytes32 # type_value) list # num list). storage_well_formed_on cx es (FST HH) ==> _`
          irule >> first_assum ACCEPT_TAC) >>
     irule for_element_copy_ghost_horizon >>
     conj_tac >- (qexistsl [`G`,`c`,`es`,`s`,`tn`] >> simp[]) >>
     qexists_tac `D` >> first_assum ACCEPT_TAC) >>
  qexistsl [`v`,`ee`,`t`,`Gf`,`tnf`] >>
  rpt (conj_tac >-
    simp[Abbr `t`, ghostPcTransportPtrTheory.ptr_covers_inst_idx,
         IgnAsm `sCopy = _ with vs_vars := _`]) >>
  first_assum ACCEPT_TAC
QED

Resume for_nonslot_array_element_prepare_full[immutable_ghost]:
  qpat_assum `ghost_inv_at D lo d c cx es GCopy tnCopy sCopy`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
  qpat_assum `(z with <|vs_vars := _; vs_memory := _|>) = sCopy`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `!p sz. not_fresh_at saCopy p /\ ptr_covers GCopy tnCopy p sCopy sz ==>
      ptr_covers Gf tnf p t sz` by
    simp[Abbr `t`,ghostPcTransportPtrTheory.ptr_covers_inst_idx] >>
  simp[bodyPtrDefsTheory.ghost_inv_at_def,
       IgnAsm `!i. i IN tnf.t_mem <=> _`] >>
  conj_tac >- suspend "immutable_ghost_locals" >>
  conj_tac >- suspend "immutable_ghost_return" >>
  conj_tac
  >- (qpat_assum `stor_taint_ok_at D tnCopy sCopy`
        (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
      simp[Abbr `t`, bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
  conj_tac >- suspend "immutable_ghost_low" >>
  simp[allocas_from_def,Abbr `t`]
QED

Resume for_nonslot_array_element_prepare_full[immutable_ghost_return]:
  Cases_on `d` >- simp[bodyPtrDefsTheory.return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME rb) _ _ _ _` >> PairCases_on `rb` >>
  qpat_assum `return_buf_frame (SOME _) c sa s`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.return_buf_frame_def]) >>
  qpat_assum `return_buf_ptr (SOME _) c GCopy tnCopy sCopy`
    (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.return_buf_ptr_def]) >>
  drule stmtFragPtrTheory.cenv_top_ext_return_buf >>
  simp[bodyPtrDefsTheory.return_buf_ptr_def] >> strip_tac >>
  `x' = x` by fs[] >>
  qpat_x_assum `x' = x` SUBST_ALL_TAC >> simp[]
QED

Resume for_nonslot_array_element_prepare_full[immutable_ghost_low]:
  `lo <= w2n dw` by
    (qpat_assum `allocas_from lo sCopy`
       (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then (qspecl_then [`aidItem`,`w2n dw`,`capacity`] mp_tac) >> simp[]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo sCopy.vs_memory` by
    (simp[Abbr `t`,NoAsms] >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _`
       (qspecl_then [`0`,`lo`] mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `~(w2n dw <= i)` by decide_tac >>
  qpat_assum `!i. i < lo /\ i IN tnCopy.t_mem ==> _`
    (qspec_then `i` mp_tac) >> fs[] >> metis_tac[]
QED

Resume for_nonslot_array_element_prepare_full[immutable_ghost_locals]:
  map_every qx_gen_tac [`name`,`ent`,`reg`,`cap`] >>
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  Cases_on `name = id`
  >- (qpat_x_assum `name = id` SUBST_ALL_TAC >>
      qpat_x_assum `lookup_scopes id (_ :: es.scopes) = SOME ent`
        (mp_tac) >>
      simp[NoAsms,vyperStateTheory.lookup_scopes_def,FLOOKUP_UPDATE] >>
      disch_then (SUBST1_TAC o SYM) >>
      qpat_assum `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var xd) capacity)`
        (fn th => qpat_x_assum `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var reg) cap)`
          (mp_tac o REWRITE_RULE [th])) >>
      simp[NoAsms] >> strip_tac >>
      qpat_assum `xd = reg` (SUBST1_TAC o SYM) >>
      qpat_assum `capacity = cap` (SUBST1_TAC o SYM) >>
      simp[Abbr `entry`]) >>
  `lookup_scopes name es.scopes = SOME ent` by
    (qpat_x_assum `lookup_scopes name (_ :: es.scopes) = SOME ent` mp_tac >>
     simp[vyperStateTheory.lookup_scopes_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY,
          Once EQ_SYM_EQ]) >>
  `FLOOKUP c.ce_vars name = SOME (PtrVar (Var reg) cap)` by
    (qpat_assum `!name. IS_SOME (lookup_scopes name es.scopes) ==> _`
       (qspec_then `name` mp_tac) >> simp[]) >>
  `not_fresh_at saCopy reg` by
    (qpat_assum `!name reg sz. FLOOKUP bc.ce_vars name = _ ==> _`
       drule >> simp[]) >>
  qpat_assum `!name entry p sz. lookup_scopes name es.scopes = SOME entry /\ _ ==> _`
    (qspecl_then [`name`,`ent`,`reg`,`cap`] mp_tac) >> simp[] >>
  strip_tac >>
  qpat_assum `stmt_state_rel H ctx func bc cx ee t`
    (strip_assume_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
  map_every qx_gen_tac [`w`,`mem`] >> DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `lookup_var reg t = lookup_var reg z` by
    simp[Abbr `t`,lookup_var_def,NoAsms] >>
  `lookup_var reg z = lookup_var reg sCopy` by
    (qpat_assum `!x. not_fresh_at saCopy x ==> lookup_var x z = _`
       (qspec_then `reg` irule) >> first_assum ACCEPT_TAC) >>
  `lookup_var reg sCopy = SOME w` by
    (qpat_assum `lookup_var reg z = lookup_var reg sCopy` (SUBST1_TAC o SYM) >>
     qpat_assum `lookup_var reg t = lookup_var reg z` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `val_wf ent.type ent.value /\ type_memory_size ent.type <= cap` by
    (qpat_assum `local_ptrs_rel func bc ee.scopes t`
       (qspecl_then [`name`,`ent`,`reg`,`cap`] mp_tac o CONJUNCT1 o
        REWRITE_RULE [local_ptrs_rel_def]) >> simp[] >> strip_tac >> simp[]) >>
  `local_region bc ee.scopes t name (w2n w) cap` by
    (simp[local_region_def] >> qexistsl [`ent`,`reg`,`w`] >> simp[]) >>
  `local_region bc ee.scopes t id (w2n dw) capacity` by
    simp[local_region_def,vyperStateTheory.lookup_scopes_def,FLOOKUP_UPDATE] >>
  `w2n w + cap <= w2n dw \/ w2n dw + capacity <= w2n w` by
    (qpat_assum `local_ptrs_rel func bc ee.scopes t`
       (qspecl_then [`name`,`id`,`w2n w`,`cap`,`w2n dw`,`capacity`] mp_tac o
        CONJUNCT2 o REWRITE_RULE [local_ptrs_rel_def]) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `stride <= capacity` by simp[] >>
  `mem_bytes_at (w2n w) cap t.vs_memory = mem_bytes_at (w2n w) cap sCopy.vs_memory` by
    (simp[Abbr `t`,NoAsms] >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _`
       (qspecl_then [`w2n w`,`cap`] mp_tac) >>
     disch_then irule >> decide_tac) >>
  `!i. w2n w <= i /\ i < w2n w + cap /\ i IN tnf.t_mem ==> i IN tnCopy.t_mem` by
    (qx_gen_tac `i` >> strip_tac >>
     `~(w2n dw <= i /\ i < w2n dw + stride)` by decide_tac >>
     qpat_assum `!i. i IN tnf.t_mem <=> _` (qspec_then `i` mp_tac) >> simp[]) >>
  `val_footprint ent.type ent.value <= cap` by
    (drule exprSimPropsTheory.val_footprint_le >> decide_tac) >>
  `!m. mem_agree_outside tnCopy.t_mem sCopy.vs_memory m ==>
       val_in_memory ent.type ent.value (w2n w) m` by
    (qpat_assum `!w m. lookup_var reg sCopy = SOME w /\ _ ==> _`
       (qspec_then `w` mp_tac) >> simp[]) >>
  drule_all bodyPtrBytestringBuiltinsWindowGhostTheory.robust_val_in_memory_window_transport >>
  simp[]
QED

Resume for_nonslot_array_element_prepare_full[memory_source]:
  `~is_word_type (post_value_type c e) /\
   ~is_bytestring_type (post_value_type c e)` by
    (qpat_assum `post_value_type c e = expr_type e` SUBST1_TAC >>
     qpat_assum `expr_type e = ArrayT sty bd` SUBST1_TAC >>
     simp[compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def, NoAsms]) >>
  `evaluate_type (get_tenv cx) (post_value_type c e) = SOME (ArrayTV stv bd)` by
    (qpat_assum `post_value_type c e = expr_type e` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `alloca_inv sCopy` by
    (qpat_assum `stmt_state_rel H ctx func c cx es sCopy`
       (ACCEPT_TAC o cj 2 o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca)) >>
  `sCopy.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel H ctx func c cx es s`
       (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_alloca_room) >>
     disch_then (assume_tac o MATCH_MP exprLoweringPropsTheory.alloca_room_next_lt) >>
     simp[]) >>
  `w2n dw + capacity <= sCopy.vs_alloca_next` by
    (qpat_assum `alloca_inv sCopy` (mp_tac o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.alloca_next_valid_def]) >> strip_tac >>
     qpat_assum `!aid base sz. FLOOKUP sCopy.vs_allocas aid = SOME (base,sz) ==> _`
       (qspecl_then [`aidItem`,`w2n dw`,`capacity`] mp_tac) >> simp[]) >>
  `bc.ce_imm_alloca = c.ce_imm_alloca` by
    (drule bodySimTheory.cenv_top_ext_same_frame >>
     simp[bodySimTheory.same_frame_def] >> strip_tac >>
     qpat_x_assum `_ = c` (SUBST1_TAC o SYM) >> simp[]) >>
  `not_local_ptr bc (FEMPTY :: es.scopes) xd` by
    (qspecl_then [`bc`,`sbCopy`,`FEMPTY :: es.scopes`,`id`,`xd`,`capacity`] mp_tac
       exprLoweringPropsTheory.local_ptrs_reserved_not_live >>
     simp[vyperStateTheory.lookup_scopes_def,FLOOKUP_EMPTY]) >>
  `not_local_ptr c es.scopes xd` by
    (qpat_assum `not_local_ptr bc (FEMPTY :: es.scopes) xd` mp_tac >>
     simp[NoAsms,not_local_ptr_def,vyperStateTheory.lookup_scopes_def,FLOOKUP_EMPTY] >>
     strip_tac >> conj_tac
     >- (rpt strip_tac >>
         `name <> id` by (strip_tac >> fs[]) >>
         qpat_assum `!name. name <> id ==> FLOOKUP bc.ce_vars name = _`
           (qspec_then `name` mp_tac) >>
         qpat_assum `name <> id` (fn th => simp[NoAsms,th]) >>
         disch_then (fn eq =>
           qpat_assum `!name entry sz. lookup_scopes name es.scopes = SOME entry ==>
                       FLOOKUP bc.ce_vars name <> _`
             (qspecl_then [`name`,`entry`,`sz`] (mp_tac o REWRITE_RULE [eq]))) >>
         simp[]) >>
     qpat_assum `bc.ce_imm_alloca = c.ce_imm_alloca` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm
    (qx_choose_then `v` (qx_choose_then `sw` (map_every assume_tac o CONJUNCTS))))
    `?v sw. EL k vs = Value v /\ value_has_type stv v /\ val_wf stv v /\
     lookup_var out sCopy = SOME sw /\
     (!mem. mem_agree_outside tnCopy.t_mem sCopy.vs_memory mem ==>
       val_in_memory stv v (w2n sw) mem) /\
     (0 < stride ==> ptr_covers GCopy tnCopy out sCopy stride) /\
     w2n sw + stride < dimword (:256) /\
     (stride = 0 \/ w2n sw + stride <= sCopy.vs_alloca_next) /\
     (w2n sw + stride <= w2n dw \/ w2n dw + stride <= w2n sw)`
  >- suspend "memory_child" >>
  suspend "memory_dispatch"
QED

Resume for_nonslot_array_element_prepare_full[memory_child]:
  Q_TAC (fn tm => SUBGOAL_THEN tm DISJ_CASES_TAC)
    `rv = Value (ArrayV av) \/ ?name path. rv = PlaceR (MemoryPlace name path)`
  >- simp[]
  >- suspend "memory_owned" >>
  pop_assum (qx_choose_then `name` (qx_choose_then `path` assume_tac)) >>
  suspend "memory_place"
QED

Resume for_nonslot_array_element_prepare_full[memory_owned]:
  `vv_own c cx (post_value_type c e) sa0 sbExpr em rv vv u` by
    (qpat_assum `!v. rv = Value v /\ _ ==> _` (qspec_then `ArrayV av` mp_tac) >> simp[]) >>
  `array_iterator_results cx (expr_type e) rv em = (INL vs,em)` by
    (qpat_assum `rv = Value (ArrayV av)` SUBST1_TAC >>
     simp[vyperInterpreterTheory.array_iterator_results_def, vyperStateTheory.bind_def,
          vyperStateTheory.read_result_def, vyperValueOperationTheory.extract_elements_def,
          vyperStateTheory.lift_option_type_def, vyperStateTheory.return_def]) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `value_has_type (ArrayTV stv bd) (ArrayV av)`
  >- simp[] >>
  suspend "memory_owned_child"
QED

Resume for_nonslot_array_element_prepare_full[memory_owned_child]:
  Q_TAC (fn tm => SUBGOAL_THEN tm
      (qx_choose_then `ann` (qx_choose_then `mp` (map_every assume_tac o CONJUNCTS))))
    `?ann mp. mp.ptr_operand = vv_operand vv /\ mp.ptr_location = LocMemory /\
      vv_own c cx (post_value_type c e) sa0 sbExpr em
        (Value (ArrayV av)) (LocatedValue ann mp) u /\
      ptr_vv_ok cx (post_value_type c e) (Value (ArrayV av))
        (LocatedValue ann mp) em Gu tu u`
  >- (Cases_on `vv`
      >- (rename1 `StackValue styTag arrOp` >>
          `read_result cx rv em = (INL (ArrayV av),em)` by
            (qpat_assum `rv = Value (ArrayV av)` SUBST1_TAC >>
             simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
          `expr_val_own c cx (post_value_type c e) sa0 sbExpr em (ArrayV av) arrOp u` by
            (qpat_assum `vv_own _ _ _ _ _ _ rv (StackValue _ _) u`
               (mp_tac o REWRITE_RULE [loweringPostsTheory.vv_own_def]) >>
             disch_then (qspec_then `ArrayV av` irule) >>
             first_assum ACCEPT_TAC) >>
          `op_taint tu arrOp = {} /\
           ptr_mem_ok cx (post_value_type c e) (ArrayV av) arrOp Gu tu u` by
            (qpat_assum `ptr_vv_ok _ _ rv (StackValue _ _) em Gu tu u` mp_tac >>
             qpat_assum `rv = Value (ArrayV av)` SUBST1_TAC >>
             simp_tac std_ss [bodyPtrDefsTheory.ptr_vv_ok_def, bodyPtrDefsTheory.ptr_val_ok_def,
                 vyperStateTheory.read_result_def, vyperStateTheory.return_def,
                 pairTheory.PAIR_EQ, sumTheory.INL_11] >>
             simp[]) >>
          qexistsl_tac [`styTag`, `mk_ptr arrOp LocMemory`] >>
          simp[NoAsms, contextTheory.mk_ptr_def, contextTheory.vv_operand_def,
               loweringPostsTheory.vv_own_def, bodyPtrDefsTheory.ptr_vv_ok_def,
               vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
          conj_tac >-
            (qpat_assum `expr_val_own _ _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_val_own_def]) >>
             disch_then (fn th => gen_tac >> disch_tac >> MATCH_MP_TAC th) >>
             conj_tac >- first_assum ACCEPT_TAC >>
             first_assum ACCEPT_TAC) >>
          asm_rewrite_tac[]) >>
      rename1 `LocatedValue styTag arrPtr` >>
      qexistsl_tac [`styTag`,`arrPtr`] >>
      qpat_assum `rv = Value (ArrayV av)` (SUBST1_TAC o SYM) >>
      simp[NoAsms, contextTheory.vv_operand_def] >>
      rpt conj_tac >- (qpat_assum `!v. rv = Value v /\ _ ==> _`
        (qspec_then `ArrayV av` mp_tac) >> simp[NoAsms] >>
        impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
        simp[NoAsms]) >>
      first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [
    `cx` |-> `cx`, `aty` |-> `expr_type e`, `av` |-> `av`, `ee` |-> `em`,
    `vs` |-> `vs`, `stv` |-> `stv`, `bd` |-> `bd`, `ty` |-> `post_value_type c e`,
    `c` |-> `c`, `sa` |-> `sa0`, `sb` |-> `sbExpr`, `p` |-> `mp`, `ann` |-> `ann`,
    `G0` |-> `Gu`, `tn0` |-> `tu`, `s` |-> `s`, `u` |-> `u`,
    `c'` |-> `c`, `es` |-> `es`, `tn` |-> `tn`, `k` |-> `k`]
    for_owned_array_current_child) >>
  impl_tac
  >- (`array_iterator_results cx (expr_type e) (Value (ArrayV av)) em = (INL vs,em)` by
        (qpat_assum `rv = Value (ArrayV av)` (SUBST1_TAC o SYM) >>
         first_assum ACCEPT_TAC) >>
      asm_rewrite_tac[] >> simp[]) >>
  disch_then (qx_choose_then `w` (qx_choose_then `v`
    (map_every assume_tac o CONJUNCTS))) >>
  `w = bw` by
    (qpat_assum `eval_operand mp.ptr_operand s = SOME w` mp_tac >>
     qpat_assum `mp.ptr_operand = vv_operand vv` SUBST1_TAC >>
     qpat_assum `eval_operand (vv_operand vv) s = SOME bw` SUBST1_TAC >> simp[]) >>
  qpat_x_assum `w = bw` SUBST_ALL_TAC >>
  `val_footprint (ArrayTV stv bd) (ArrayV av) = type_memory_size (ArrayTV stv bd)` by
    simp[loweringPostsTheory.val_footprint_def] >>
  `?cap h. h = (case bd of Fixed _ => 0 | Dynamic _ => 32) /\
           k < cap /\ type_memory_size (ArrayTV stv bd) = h + cap * stride` by
    (`k < LENGTH (array_elements (ArrayTV stv bd) av)` by
       (qpat_assum `k < LENGTH vs` mp_tac >>
        qpat_assum `vs = MAP Value xs` SUBST1_TAC >>
        qpat_assum `extract_elements _ (ArrayV av) = SOME xs` mp_tac >>
        simp[NoAsms, vyperValueOperationTheory.extract_elements_def] >>
        disch_then (SUBST1_TAC o SYM) >> simp[]) >>
     qpat_assum `value_has_type (ArrayTV stv bd) (ArrayV av)` mp_tac >>
     qpat_assum `k < LENGTH (array_elements _ av)` mp_tac >>
     qpat_assum `stride = type_memory_size dtv` SUBST1_TAC >>
     qpat_assum `stv = dtv` (SUBST1_TAC o SYM) >>
     namedCases_on `bd` ["cap", "cap"] >> Cases_on `av` >>
     simp[NoAsms, vyperTypingTheory.value_has_type_inv,
          vyperValueOperationTheory.array_elements_def, valueEncodingTheory.type_memory_size_def] >>
     rpt strip_tac >> qexists_tac `cap` >> simp[] >> decide_tac) >>
  `h = (if dyn then 32 else 0)` by (Cases_on `bd` >> simp[]) >>
  `h + k*stride + stride <= type_memory_size (ArrayTV stv bd)` by
    (`SUC k * stride <= cap * stride` by (irule LESS_MONO_MULT >> simp[]) >>
     qpat_assum `type_memory_size (ArrayTV stv bd) = h + cap * stride` SUBST1_TAC >>
     qpat_assum `SUC k * stride <= cap * stride` (mp_tac o REWRITE_RULE [MULT_CLAUSES]) >>
     decide_tac) >>
  suspend "memory_owned_bounds"
QED

Resume for_nonslot_array_element_prepare_full[memory_owned_bounds]:
  qabbrev_tac `off = h + k*stride` >>
  qabbrev_tac `sz = type_memory_size (ArrayTV stv bd)` >>
  `lookup_var out sCopy = SOME (bw + n2w off)` by
    (qpat_assum `h = (if dyn then 32 else 0)` (SUBST1_TAC o SYM) >>
     simp[Abbr`off`]) >>
  `sz <> 0 ==> w2n bw + sz <= sCopy.vs_alloca_next /\
    (w2n bw + sz <= w2n dw \/ w2n dw + capacity <= w2n bw)` by
    suspend "memory_owned_frontier" >>
  Q_TAC (fn tm => SUBGOAL_THEN tm (map_every assume_tac o CONJUNCTS))
    `w2n bw + off + stride < dimword (:256) /\
     (stride = 0 \/ w2n bw + off + stride <= sCopy.vs_alloca_next) /\
     (w2n bw + off + stride <= w2n dw \/ w2n dw + stride <= w2n bw + off)`
  >- (Cases_on `sz = 0`
      >- (`w2n bw < dimword (:256)` by simp[NoAsms, wordsTheory.w2n_lt] >> decide_tac) >>
      qpat_assum `sz <> 0 ==> _ /\ _` drule >> strip_tac >>
      `stride = capacity` by metis_tac[] >> decide_tac) >>
  `w2n (bw + n2w off) = w2n bw + off` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `!mem. mem_agree_outside tnCopy.t_mem sCopy.vs_memory mem ==>
     val_in_memory stv v (w2n bw + off) mem` by
    (qpat_assum `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> _` mp_tac >>
     qpat_assum `sCopy.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
     qpat_assum `tnCopy.t_mem = tn.t_mem` (SUBST1_TAC o SYM) >>
     qpat_assum `h = (case bd of Fixed _ => 0 | Dynamic _ => 32)` (SUBST1_TAC o SYM) >>
     qpat_assum `stv = dtv` (fn ty =>
       qpat_assum `stride = type_memory_size dtv` (fn size =>
         simp[NoAsms, Abbr`off`,ty,size,AC ADD_ASSOC ADD_COMM]))) >>
  `0 < stride ==> ptr_covers GCopy tnCopy out sCopy stride` by suspend "memory_owned_cover" >>
  qexistsl [`v`,`bw + n2w off`] >>
  qpat_assum `w2n (bw + n2w off) = w2n bw + off` (fn th => REWRITE_TAC [th]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_nonslot_array_element_prepare_full[memory_owned_frontier]:
  disch_tac >>
  qpat_assum `val_footprint (ArrayTV stv bd) (ArrayV av) = 0 \/ _` mp_tac >>
  qpat_assum `val_footprint (ArrayTV stv bd) (ArrayV av) = sz` SUBST1_TAC >>
  simp[NoAsms] >>
  qpat_assum `sz <> 0` (fn th => simp[NoAsms, th]) >>
  disch_then (qx_choosel_then [`aid`,`b`,`len`] (map_every assume_tac o CONJUNCTS)) >>
  `FLOOKUP sCopy.vs_allocas aid = SOME (b,len)` by simp[] >>
  conj_tac >-
    (qpat_assum `alloca_inv sCopy` (mp_tac o cj 2 o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def]) >>
     simp[NoAsms, venomMemDefsTheory.alloca_next_valid_def] >>
     disch_then (qspecl_then [`aid`,`b`,`len`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> decide_tac) >>
  `aid <> aidItem` by decide_tac >>
  qpat_assum `alloca_inv sCopy`
    (mp_tac o cj 1 o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def]) >>
  simp[NoAsms, venomMemDefsTheory.allocas_non_overlapping_def] >>
  disch_then (qspecl_then [`aid`,`aidItem`,`b`,`len`,`w2n dw`,`capacity`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  decide_tac
QED

Resume for_nonslot_array_element_prepare_full[memory_owned_cover]:
  disch_tac >>
  `sz <> 0` by decide_tac >>
  `ptr_mem_ok cx (post_value_type c e) (ArrayV av) (vv_operand vv) Gu tu u` by
    (qpat_assum `mp.ptr_operand = vv_operand vv` (SUBST1_TAC o SYM) >>
     qpat_assum `ptr_vv_ok _ _ (Value (ArrayV av)) (LocatedValue ann mp) em Gu tu u`
       (mp_tac o cj 3 o REWRITE_RULE [bodyPtrDefsTheory.ptr_vv_ok_def]) >>
     qpat_assum `mp.ptr_location = LocMemory` (fn th =>
       simp[NoAsms,th,vyperStateTheory.read_result_def,vyperStateTheory.return_def])) >>
  qpat_assum `ptr_mem_ok _ _ _ _ Gu tu u`
    (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_mem_ok_def]) >>
  disch_then (qspecl_then [`ArrayTV stv bd`,`bw`] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o cj 2) >>
  impl_tac >-
    (qpat_assum `val_footprint (ArrayTV stv bd) (ArrayV av) = sz` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (sz = _)` (fn th =>
    simp[NoAsms,exprSimPropsTheory.val_store_size_def,
         SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  disch_then (qx_choosel_then [`x`,`b`,`len`] (map_every assume_tac o CONJUNCTS)) >>
  `FLOOKUP GCopy out = FLOOKUP Gu x` by
    (qpat_assum `op_prov GCopy (Var out) = op_prov G (vv_operand vv)` mp_tac >>
     qpat_assum `op_prov G (vv_operand vv) = op_prov Gu (vv_operand vv)` SUBST1_TAC >>
     qpat_assum `vv_operand vv = Var x` SUBST1_TAC >>
     simp[NoAsms,ptrDisciplineTheory.op_prov_def]) >>
  simp[NoAsms, bodyPtrDefsTheory.ptr_covers_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`bw + n2w off`,`b`,`len`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `FLOOKUP GCopy out = FLOOKUP Gu x` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `w2n (bw + n2w off) = w2n bw + off` SUBST1_TAC >> decide_tac
QED

Resume for_nonslot_array_element_prepare_full[memory_place]:
  `?ann p. vv = LocatedValue ann p` by
    (Cases_on `vv` >-
       (rename1 `StackValue ann op` >>
        qpat_assum `vv_post H ctx func c cx e es0 sa0 sbExpr s0 em rv
                         (StackValue ann op) u`
          (mp_tac o cj 4 o REWRITE_RULE [loweringPostsTheory.vv_post_def]) >>
        qpat_assum `rv = PlaceR (MemoryPlace name path)` SUBST1_TAC >>
        qpat_assum `~is_word_type (post_value_type c e)` (fn th =>
          simp[NoAsms,th,loweringPostsTheory.vv_at_def])) >>
     simp[NoAsms]) >>
  qpat_assum `vv_post H ctx func c cx e es0 sa0 sbExpr s0 em rv vv u`
    (assume_tac o cj 5 o REWRITE_RULE [loweringPostsTheory.vv_post_def]) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm
    (qx_choosel_then [`root`,`room`,`rw`,`rootTy`,`rootTV`,`delta`,`pathTV`]
       (map_every assume_tac o CONJUNCTS)))
    `?root room rw rootTy rootTV delta pathTV.
       FLOOKUP c.ce_vars name = SOME (PtrVar (Var root) room) /\
       lookup_var root u = SOME rw /\
       c.ce_var_type name = SOME rootTy /\
       evaluate_type (get_tenv cx) rootTy = SOME rootTV /\
       mem_path_offset rootTV path = SOME (delta,pathTV) /\
       eval_operand (vv_operand vv) u = SOME (rw + n2w delta)`
  >- (qpat_assum `vv_place_ptr c cx em u rv vv` mp_tac >>
      qpat_assum `rv = PlaceR (MemoryPlace name path)` SUBST1_TAC >>
      qpat_assum `vv = LocatedValue ann p` SUBST1_TAC >>
      simp[NoAsms,loweringPostsTheory.vv_place_ptr_def,contextTheory.vv_operand_def] >>
      metis_tac[]) >>
  `lookup_var root s = SOME rw` by
    (qpat_assum `!name path root sz w. rv = PlaceR (MemoryPlace name path) /\ _ ==> _`
       (qspecl_then [`name`,`path`,`root`,`room`,`rw`] mp_tac) >> simp[]) >>
  `not_fresh_at sa root` by
    (qpat_assum `local_ptrs_reserved c sa`
       (mp_tac o cj 2 o REWRITE_RULE [local_ptrs_reserved_def]) >>
     disch_then (qspecl_then [`name`,`name`,`root`,`room`,`room`] mp_tac) >>
     simp[]) >>
  `lookup_var root sCopy = SOME rw` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x sCopy = lookup_var x s`
       (qspec_then `root` mp_tac) >> simp[]) >>
  suspend "memory_place_child"
QED

Resume for_nonslot_array_element_prepare_full[memory_dispatch]:
  `read_result cx (EL k vs) es = (INL v,es)` by
    simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  `value_has_type dtv v /\ val_wf dtv v` by
    (qpat_assum `stv = dtv` (SUBST1_TAC o SYM) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `entry = <|assignable := F; type := dtv; value := v; popped := []|>` >>
  qabbrev_tac `ee = es with scopes updated_by CONS (FEMPTY |+ (id,entry))` >>
  `push_scope_with_var id dtv v es = (INL (),ee)` by
    simp[Abbr`ee`, Abbr`entry`, vyperStateTheory.push_scope_with_var_def,
         vyperStateTheory.return_def] >>
  `compile_iter_elem_copy c (Var out) (Var xd) stride LocMemory F fty fty
      saCopy = ((),sbCopy)` by
    (qpat_assum `compile_iter_elem_copy c addr (Var xd) stride loc
       (is_slot_addressed loc) fty sty saCopy = ((),sbCopy)` mp_tac >>
     qpat_assum `loc = LocMemory` (fn th => REWRITE_TAC [th]) >>
     qpat_assum `addr = Var out` (fn th => REWRITE_TAC [th]) >>
     qpat_assum `sty = fty` (fn th => REWRITE_TAC [th]) >>
     simp[is_slot_addressed_def, NoAsms]) >>
  `type_widens_to (get_tenv cx) fty fty` by
    simp[vyperTypeArgFitsTheory.type_widens_to_refl] >>
  `acyclic_struct_metadata c.ce_struct_fields /\
   sfields_tenv_consistent c.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP c.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields)` by
    (drule_then assume_tac bodySimTheory.body_inv_contract >>
     drule_then assume_tac contract_inv_acyclic_struct_metadata >>
     qpat_assum `expr_sim_inv c cx env es`
       (map_every assume_tac o CONJUNCTS o
        REWRITE_RULE [exprSimHypsDefsTheory.expr_sim_inv_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `allocas_from lo sCopy /\ (ctx_has_dalloca ctx ==> allocas_below_fmp sCopy)` by
    (`allocas_from lo sCopy = allocas_from lo s /\
       allocas_below_fmp sCopy = allocas_below_fmp s` by
       (REWRITE_TAC[allocas_from_def, allocas_below_fmp_def] >>
        qpat_assum `sCopy.vs_allocas = s.vs_allocas` SUBST1_TAC >>
        qpat_assum `sCopy.vs_initial_fmp = s.vs_initial_fmp` SUBST1_TAC >>
        qpat_assum `sCopy.vs_fmp = s.vs_fmp` SUBST1_TAC >> simp[NoAsms]) >>
     qpat_assum `allocas_from lo sCopy = allocas_from lo s` SUBST1_TAC >>
     qpat_assum `allocas_below_fmp sCopy = allocas_below_fmp s` SUBST1_TAC >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `lo <= sCopy.vs_alloca_next` by
    (qpat_assum `sCopy.vs_alloca_next = s.vs_alloca_next` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `w2n dw + stride < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST
    [`c` |-> `c`, `xs` |-> `out`, `xd` |-> `xd`, `bytes` |-> `stride`,
     `dty` |-> `fty`, `sty` |-> `fty`, `sa` |-> `saCopy`, `sb` |-> `sbCopy`,
     `k` |-> `k`, `vs` |-> `vs`, `v` |-> `v`, `tenv` |-> `get_tenv cx`,
     `stv` |-> `stv`, `dtv` |-> `dtv`, `tn` |-> `tnCopy`, `s` |-> `sCopy`,
     `sw` |-> `sw`, `G` |-> `GCopy`, `dw` |-> `dw`, `aid` |-> `aidItem`,
     `capacity` |-> `capacity`, `lo` |-> `lo`, `ctx` |-> `ctx`, `func` |-> `func`,
     `explicit` |-> `explicit`, `PG` |-> `PG`]
    (SPEC_ALL for_memory_element_dispatch_joint_frame)) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_assum `stv = dtv` SUBST1_TAC >>
      TRY (first_assum ACCEPT_TAC) >>
      qpat_assum `stride = type_memory_size dtv` (SUBST1_TAC o SYM) >>
      TRY (first_assum ACCEPT_TAC) >>
      simp[vyperTypeArgFitsTheory.type_widens_to_refl]) >>
  disch_then (qx_choose_then `n` (qx_choose_then `t` (qx_choose_then `Gf`
    (qx_choose_then `tnf` (map_every assume_tac o CONJUNCTS))))) >>
  suspend "memory_frame"
QED

Resume for_nonslot_array_element_prepare_full[memory_frame]:
  qpat_assum `typed_copy_state_frame saCopy (w2n dw) n sCopy t`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [typed_copy_state_frame_def,
       typed_copy_frame_def]) >>
  qpat_assum `(t with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
       vs_current_bb := _; vs_inst_idx := _|>) = sCopy`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `copy_static t = copy_static sCopy` by
    simp[exprSimStorageCopyTheory.copy_static_def, venom_state_component_equality] >>
  `sa.cs_next_var <= saCopy.cs_next_var` by
    (qpat_assum `emit_op MUL _ sa = _`
       (strip_assume_tac o MATCH_MP exprSimAccountsTheory.emit_op_extends_next_var) >>
     qpat_assum `emit_op ADD _ sn = (_,saCopy)`
       (strip_assume_tac o MATCH_MP exprSimAccountsTheory.emit_op_extends_next_var) >>
     `sm.cs_next_var <= sn.cs_next_var` suffices_by decide_tac >>
     qpat_assum `(if dyn then emit_op ADD [Lit 32w;offOp] sm = _ else _)` mp_tac >>
     Cases_on `dyn` >> simp[NoAsms] >>
     metis_tac[exprSimAccountsTheory.emit_op_extends_next_var]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at saCopy x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)` by
    (qx_gen_tac `Dx` >> qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK sCopy,GCopy,tnCopy)`
       (qspec_then `Dx` (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
     simp[]) >>
  qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)` (qspec_then `D` assume_tac) >>
  `alloca_history func t` by
    (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gf,tnf)` (irule_at Any) >>
     qpat_assum `stmt_state_rel H ctx func c cx es s`
       (strip_assume_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `saCopy.cs_next_var <= sbCopy.cs_next_var` by
    (qpat_assum `compile_iter_elem_copy c (Var out) (Var xd) stride LocMemory F fty fty
        saCopy = ((),sbCopy)` (fn eq =>
       qspecl_then [`c`,`Var out`,`Var xd`,`stride`,`LocMemory`,`F`,`fty`,`fty`,`saCopy`]
         (mp_tac o REWRITE_RULE [eq, pairTheory.SND, ci_mono_def])
         (cj 6 stmtLoweringMonoTheory.ci_mono_stmt_helpers)) >>
     simp[NoAsms]) >>
  `return_buf_frame d bc sbCopy t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl [`c`,`s`,`sa`] >>
     drule stmtFragPtrTheory.cenv_top_ext_return_buf >> simp[] >>
     rpt strip_tac >> decide_tac) >>
  `ee.scopes = (FEMPTY |+ (id,entry)) :: es.scopes` by simp[Abbr`ee`] >>
  `ee = es with scopes := ee.scopes` by
    simp[Abbr`ee`, vyperStateTheory.evaluation_state_component_equality] >>
  `!(HH:(bool # bytes32 # type_value) list # num list). storage_well_formed_on cx es (FST HH) ==> storage_well_formed_on cx ee (FST HH)` by
    (qx_gen_tac `HH` >> disch_tac >>
     qpat_assum `ee = es with scopes := _` (fn th => simp[Once th, NoAsms,
       vyperStorageFootprintTheory.storage_well_formed_on_def,
       vyperStorageBackendTheory.get_storage_scopes]) >>
     qpat_assum `storage_well_formed_on cx es (FST HH)`
       (ACCEPT_TAC o REWRITE_RULE [vyperStorageFootprintTheory.storage_well_formed_on_def])) >>
  suspend "memory_frame_binding"
QED

Resume for_nonslot_array_element_prepare_full[memory_frame_binding]:
  qabbrev_tac `empty = es with scopes := FEMPTY :: es.scopes` >>
  `!(HH:(bool # bytes32 # type_value) list # num list). stmt_state_rel HH ctx func c cx es s ==>
      stmt_state_rel HH ctx func bc cx empty sCopy` by
    (gen_tac >> disch_tac >> simp[Abbr `empty`,NoAsms] >>
     irule array_empty_scope_rel_transport >> qexists_tac `c` >>
     simp[] >>
     qpat_assum `!(HH:(bool # bytes32 # type_value) list # num list). stmt_state_rel HH ctx func c cx es s ==> stmt_state_rel HH ctx func c cx es sCopy`
       irule >> first_assum ACCEPT_TAC) >>
  `!nm reg sz. FLOOKUP bc.ce_vars nm = SOME (PtrVar (Var reg) sz) ==>
     not_fresh_at saCopy reg` by
    (rpt gen_tac >> strip_tac >> Cases_on `nm = id`
     >- (qpat_x_assum `FLOOKUP bc.ce_vars nm = SOME _` mp_tac >>
         simp[] >> disch_then (SUBST1_TAC o SYM o CONJUNCT1) >> simp[]) >>
     `FLOOKUP c.ce_vars nm = SOME (PtrVar (Var reg) sz)` by
       (qpat_assum `!nm. nm <> id ==> FLOOKUP bc.ce_vars nm = FLOOKUP c.ce_vars nm`
          (qspec_then `nm` mp_tac) >> simp[] >>
        disch_then (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     qpat_assum `local_ptrs_reserved c saCopy`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     qpat_assum `!n1 n2 x sz1 sz2. FLOOKUP c.ce_vars n1 = _ ==> _`
       (qspecl_then [`nm`,`nm`,`reg`,`sz`,`sz`] mp_tac) >> simp[]) >>
  `local_ptrs_reserved bc saCopy` by
    (qpat_assum `local_ptrs_reserved bc sbCopy`
       (mp_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     simp[local_ptrs_reserved_def] >> strip_tac >> rpt conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!nm reg sz. FLOOKUP bc.ce_vars nm = _ ==> not_fresh_at saCopy reg`
           irule >> goal_assum (drule_at Any)) >>
     rpt strip_tac >> simp[] >> irule local_ptrs_reserved_imm_base >>
     qexists_tac `c` >> simp[]) >>
  qpat_assum `?inst. MEM inst (fn_insts func) /\ _`
    (qx_choose_then `itemInst` (map_every assume_tac o CONJUNCTS)) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `!(HH:(bool # bytes32 # type_value) list # num list). stmt_state_rel HH ctx func c cx es s ==> stmt_state_rel HH ctx func bc cx ee t`
  >- suspend "memory_binding_rel" >>
  `stmt_state_rel H ctx func bc cx ee t` by
    (qpat_assum `!(HH:(bool # bytes32 # type_value) list # num list). stmt_state_rel HH ctx func c cx es s ==> stmt_state_rel HH ctx func bc cx ee t`
       irule >> first_assum ACCEPT_TAC) >>
  suspend "memory_outer_frames"
QED

Resume for_nonslot_array_element_prepare_full[memory_binding_rel]:
  `ee = empty with scopes := (FEMPTY |+ (id,entry)) :: es.scopes` by
    simp[Abbr`ee`, Abbr`empty`,NoAsms, vyperStateTheory.evaluation_state_component_equality] >>
  qpat_assum `ee = _` SUBST1_TAC >>
  qpat_assum `Abbrev (entry = _)`
    (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qx_gen_tac `HH` >> disch_tac >>
  `stmt_state_rel HH ctx func bc cx empty sCopy` by
    (qpat_assum `!(HH:(bool # bytes32 # type_value) list # num list). stmt_state_rel HH ctx func c cx es s ==> stmt_state_rel HH ctx func bc cx empty sCopy`
       irule >> first_assum ACCEPT_TAC) >>
  irule stmtSimDeclCopyFrameTheory.stmt_state_rel_declare_copy_frame >>
  simp[Abbr`empty`, vyperStateTheory.lookup_scopes_def] >>
  qexistsl [`itemInst`,`sCopy`,`saCopy`,`dw`] >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _`
    (qspecl_then [`b`,`n'`] mp_tac) >>
  qpat_assum `sCopy.vs_memory = s.vs_memory` (fn th => REWRITE_TAC [th]) >>
  disch_then irule >> decide_tac
QED

Resume for_nonslot_array_element_prepare_full[memory_outer_frames]:
  `venomMemDefs$allocas_non_overlapping sCopy` by
    (qpat_assum `alloca_inv sCopy`
       (ACCEPT_TAC o cj 1 o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def])) >>
  `!aid off sz. FLOOKUP sCopy.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id ==>
     off + sz <= w2n dw \/ w2n dw + capacity <= off` by
    (rpt gen_tac >> strip_tac >>
     `aid <> aidItem` by decide_tac >>
     qpat_assum `allocas_non_overlapping sCopy`
       (mp_tac o REWRITE_RULE [venomMemDefsTheory.allocas_non_overlapping_def]) >>
     disch_then (qspecl_then [`aid`,`aidItem`,`off`,`sz`,`w2n dw`,`capacity`] mp_tac) >> simp[]) >>
  `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
     aid < sa0.cs_next_id /\
     (!name b len. local_region c es0.scopes s0 name b len ==>
       off + sz <= b \/ b + len <= off) /\
     off <= i /\ i < off + sz /\ i IN tnf.t_mem ==> i IN tn0.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `off + sz <= w2n dw \/ w2n dw + capacity <= off` by
       (qpat_assum `!aid off sz. FLOOKUP sCopy.vs_allocas aid = _ /\ _ ==> _`
          (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[]) >>
     `~(w2n dw <= i /\ i < w2n dw+n)` by decide_tac >>
     `i IN tn.t_mem` by
       (qpat_assum `!i. _ ==> (i IN tnf.t_mem <=> _)` (qspec_then `i` mp_tac) >> simp[]) >>
     qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> i IN tn0.t_mem`
       (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >> simp[] >>
     disch_then irule >> first_assum ACCEPT_TAC) >>
  `alloca_frame c es0 sa0 s0 bc ee t` by suspend "memory_alloca_frame" >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC) `ghost_inv_at D lo d bc cx ee Gf tnf t`
  >- suspend "memory_ghost" >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
   t.vs_initial_fmp = s.vs_initial_fmp` by simp[] >>
  `allocas_from lo t` by
    (REWRITE_TAC [allocas_from_def] >>
     qpat_assum `t.vs_allocas = s.vs_allocas` SUBST1_TAC >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (REWRITE_TAC [allocas_below_fmp_def] >>
     qpat_assum `t.vs_allocas = s.vs_allocas` SUBST1_TAC >>
     qpat_assum `t.vs_fmp = s.vs_fmp` SUBST1_TAC >>
     qpat_assum `t.vs_initial_fmp = s.vs_initial_fmp` SUBST1_TAC >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
       (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def])) >>
  `!x. not_fresh_at sa0 x ==>
        FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >> `not_fresh_at sa x` by simp[] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
       (qspec_then `x` mp_tac) >>
     simp[]) >>
  `typed_copy_frame (w2n dw) capacity s.vs_memory t.vs_memory` by
    (irule typed_copy_frame_subinterval >> qexistsl [`w2n dw`,`n`] >>
     qpat_assum `sCopy.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
     simp[typed_copy_frame_def, NoAsms] >>
     rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >>
     qx_gen_tac `offset` >> qx_gen_tac `length` >> disch_tac >>
     qpat_assum `!a n'. _ ==> mem_bytes_at a n' t.vs_memory = _`
       (qspecl_then [`offset`,`length`] MATCH_MP_TAC) >> decide_tac) >>
  `!i. ~(w2n dw <= i /\ i < w2n dw + capacity) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >>
     `~(w2n dw <= i /\ i < w2n dw + n)` by decide_tac >>
     qpat_assum `!i. _ ==> (i IN tnf.t_mem <=> _)`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `copy_static t = copy_static s` by
    (qpat_assum `copy_static t = copy_static sCopy` SUBST1_TAC >>
     qpat_assum `sCopy = _ with <|vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|>`
       (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[exprSimStorageCopyTheory.copy_static_def, NoAsms]) >>
  `!HH. valid_horizon cx st0 HH es.storage_trace ==>
     stmt_state_rel HH ctx func bc cx ee t /\ storage_well_formed_on cx ee (FST HH) /\
     ghost_inv_at (DF HH) lo d bc cx ee Gf tnf t` by
    (qx_gen_tac `HH` >> disch_tac >>
     qpat_assum `!HH. valid_horizon cx st0 HH es.storage_trace ==> _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     conj_tac >-
       (qpat_assum `!(HH:(bool # bytes32 # type_value) list # num list). stmt_state_rel HH ctx func c cx es s ==> stmt_state_rel HH ctx func bc cx ee t`
          irule >> first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qpat_assum `!(HH:(bool # bytes32 # type_value) list # num list). storage_well_formed_on cx es (FST HH) ==> _`
          irule >> first_assum ACCEPT_TAC) >>
     irule for_element_copy_ghost_horizon >>
     conj_tac >- (qexistsl [`G`,`c`,`es`,`s`,`tn`] >> simp[]) >>
     qexists_tac `D` >> first_assum ACCEPT_TAC) >>
  qexistsl [`v`,`ee`,`t`,`Gf`,`tnf`] >>
  simp[] >> rpt conj_tac >> rpt strip_tac >> simp[] >>
  qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> i IN tn0.t_mem`
    (qspecl_then [`aid`,`off`,`sz`,`i`] MATCH_MP_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_nonslot_array_element_prepare_full[memory_alloca_frame]:
  `!name b len. local_region bc empty.scopes sCopy name b len <=>
                local_region bc empty.scopes s name b len` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     map_every qx_gen_tac [`live`,`entLive`,`regLive`,`capLive`] >> strip_tac >>
     `lookup_scopes live es.scopes = SOME entLive` by
       (qpat_assum `lookup_scopes live empty.scopes = SOME entLive` mp_tac >>
        simp[NoAsms, Abbr `empty`, vyperStateTheory.lookup_scopes_def,FLOOKUP_EMPTY]) >>
     `live <> id` by
       (strip_tac >>
        qpat_assum `lookup_scopes live es.scopes = SOME entLive` mp_tac >>
        qpat_assum `live = id` SUBST1_TAC >>
        qpat_assum `lookup_scopes id es.scopes = NONE` (fn th => simp[NoAsms, th])) >>
     `FLOOKUP c.ce_vars live = SOME (PtrVar (Var regLive) capLive)` by
       (qpat_assum `!name. name <> id ==> _` (qspec_then `live` mp_tac) >> simp[]) >>
     `not_fresh_at sa regLive` by
       (qpat_assum `local_ptrs_reserved c sa`
          (mp_tac o cj 2 o REWRITE_RULE [local_ptrs_reserved_def]) >>
        disch_then (qspecl_then [`live`,`live`,`regLive`,`capLive`,`capLive`] mp_tac) >>
        simp[]) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x sCopy = _` irule >>
     first_assum ACCEPT_TAC) >>
  `alloca_frame c es0 sa0 s0 bc empty sCopy` by
    (qpat_assum `alloca_frame c es0 sa0 s0 bc (es with scopes updated_by CONS FEMPTY) s`
       (mp_tac o REWRITE_RULE [stmtSimDefsTheory.alloca_frame_def]) >>
     REWRITE_TAC [stmtSimDefsTheory.alloca_frame_def] >>
     simp[Abbr `empty`]) >>
  irule stmtSimDefsTheory.alloca_frame_trans >>
  qexistsl [`bc`,`empty`,`sCopy`,`sa0`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >>
  `alloca_frame bc empty sa0 sCopy bc empty sCopy` by
    (irule stmtSimDefsTheory.alloca_frame_same >> simp[NoAsms]) >>
  `!aid off z'. FLOOKUP sCopy.vs_allocas aid = SOME (off,z') /\
        aid < sa0.cs_next_id ==>
        mem_bytes_at off z' t.vs_memory = mem_bytes_at off z' sCopy.vs_memory` by
    (rpt gen_tac >> strip_tac >>
     Q.SUBGOAL_THEN `off + z' <= w2n dw \/ w2n dw + capacity <= off` ASSUME_TAC
     >- (qpat_assum `!aid off sz. FLOOKUP sCopy.vs_allocas aid = _ /\ _ ==> _`
           (qspecl_then [`aid`,`off`,`z'`] MATCH_MP_TAC) >>
         conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _`
       (qspecl_then [`off`,`z'`] MATCH_MP_TAC) >>
     decide_tac) >>
  irule stmtSimDeclComposeTheory.alloca_frame_declare_store >>
  qexistsl [`aidItem`,`entry`,`empty`,`id`,`xd`,`es.scopes`,
           `sCopy`,`sa0`,`saCopy`,`FEMPTY`,`dw`,`capacity`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[Abbr `empty`]
QED

Resume for_nonslot_array_element_prepare_full[memory_ghost]:
  `!p sz. not_fresh_at saCopy p /\ ptr_covers GCopy tnCopy p sCopy sz ==>
       ptr_covers Gf tnf p t sz` by
    (rpt strip_tac >> irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl [`GCopy`,`sCopy`,`tnCopy`] >> simp[]) >>
  `bc.ce_return_buf = c.ce_return_buf /\ bc.ce_return_pc = c.ce_return_pc` by
    (conj_tac
     >- (drule stmtFragPtrTheory.cenv_top_ext_return_buf >> simp[]) >>
     drule stmtSimPropsTheory.cenv_top_ext_return_pc >> simp[]) >>
  qpat_assum `ghost_inv_at D lo d c cx es GCopy tnCopy sCopy`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
  simp[bodyPtrDefsTheory.ghost_inv_at_def] >>
  conj_tac >- suspend "memory_ghost_locals" >>
  conj_tac
  >- (Cases_on `d` >- simp[bodyPtrDefsTheory.return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb) _ _ _ _` >> PairCases_on `rb` >>
      qpat_x_assum `return_buf_frame (SOME _) c sa s`
        (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.return_buf_frame_def]) >>
      qpat_x_assum `return_buf_ptr (SOME _) c GCopy tnCopy sCopy`
        (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.return_buf_ptr_def]) >>
      simp[bodyPtrDefsTheory.return_buf_ptr_def] >>
      fs[] >> metis_tac[]) >>
  conj_tac
  >- (REWRITE_TAC [bodyPtrDefsTheory.stor_taint_ok_at_def] >>
      qpat_assum `tnf.t_stor = tnCopy.t_stor` SUBST1_TAC >>
      qpat_assum `tnf.t_trans = tnCopy.t_trans` SUBST1_TAC >>
      qpat_assum `tnf.t_imm = tnCopy.t_imm` SUBST1_TAC >>
      qpat_assum `t.vs_call_ctx = sCopy.vs_call_ctx` SUBST1_TAC >>
      qpat_assum `t.vs_accounts = sCopy.vs_accounts` SUBST1_TAC >>
      qpat_assum `t.vs_transient = sCopy.vs_transient` SUBST1_TAC >>
      qpat_assum `t.vs_immutables = sCopy.vs_immutables` SUBST1_TAC >>
      qpat_assum `stor_taint_ok_at D tnCopy sCopy`
        (ACCEPT_TAC o REWRITE_RULE [bodyPtrDefsTheory.stor_taint_ok_at_def])) >>
  conj_tac
  >- (`lo <= w2n dw` by
        (qpat_assum `allocas_from lo sCopy`
           (qspecl_then [`aidItem`,`w2n dw`,`capacity`] MATCH_MP_TAC o
            REWRITE_RULE [allocas_from_def]) >> first_assum ACCEPT_TAC) >>
      `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo sCopy.vs_memory` by
        (qpat_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _`
           (qspecl_then [`0`,`lo`] mp_tac) >> simp[]) >>
      rpt gen_tac >> strip_tac >>
      `i < w2n dw` by
        (irule LESS_LESS_EQ_TRANS >> qexists_tac `lo` >> conj_tac >>
         first_assum ACCEPT_TAC) >>
      `~(w2n dw <= i /\ i < w2n dw+n)` by
        (qpat_assum `i < w2n dw` (assume_tac o REWRITE_RULE [GSYM NOT_LESS_EQUAL]) >>
         simp[]) >>
      `i IN tnCopy.t_mem` by
        (qpat_assum `!i. _ ==> (i IN tnf.t_mem <=> _)` (qspec_then `i` mp_tac) >> simp[]) >>
      qpat_assum `mem_bytes_at 0 lo t.vs_memory = _` SUBST1_TAC >>
      qpat_assum `!i. i < lo /\ i IN tnCopy.t_mem ==> _`
        (qspec_then `i` MATCH_MP_TAC) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at saCopy x` by metis_tac[local_ptrs_reserved_imm_base] >> simp[]) >>
  REWRITE_TAC [allocas_from_def] >>
  qpat_assum `t.vs_allocas = sCopy.vs_allocas` SUBST1_TAC >>
  qpat_assum `allocas_from lo sCopy` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])
QED

Resume for_nonslot_array_element_prepare_full[memory_ghost_locals]:
  map_every qx_gen_tac [`name`,`ent`,`reg`,`cap`] >>
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  Cases_on `name = id`
  >- (qpat_x_assum `name = id` SUBST_ALL_TAC >>
      qpat_x_assum `lookup_scopes id (_ :: es.scopes) = SOME ent` mp_tac >>
      simp[NoAsms,vyperStateTheory.lookup_scopes_def,FLOOKUP_UPDATE] >>
      disch_then (SUBST1_TAC o SYM) >>
      qpat_assum `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var xd) capacity)`
        (fn th => qpat_x_assum `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var reg) cap)`
          (mp_tac o REWRITE_RULE [th])) >>
      simp[NoAsms] >> strip_tac >>
      qpat_assum `xd = reg` (SUBST1_TAC o SYM) >>
      qpat_assum `capacity = cap` (SUBST1_TAC o SYM) >>
      simp[Abbr`entry`]) >>
  `lookup_scopes name es.scopes = SOME ent` by
    (qpat_x_assum `lookup_scopes name (_ :: es.scopes) = SOME ent` mp_tac >>
     simp[vyperStateTheory.lookup_scopes_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY]) >>
  `FLOOKUP c.ce_vars name = SOME (PtrVar (Var reg) cap)` by
    (qpat_assum `!name. name <> id ==> _` (qspec_then `name` mp_tac) >> simp[]) >>
  `not_fresh_at saCopy reg` by
    (qpat_assum `!name reg sz. FLOOKUP bc.ce_vars name = _ ==> _` drule >> simp[]) >>
  qpat_assum `!name entry p sz. lookup_scopes name es.scopes = SOME entry /\ _ ==> _`
    (qspecl_then [`name`,`ent`,`reg`,`cap`] mp_tac) >> simp[] >>
  strip_tac >>
  map_every qx_gen_tac [`w`,`mem`] >> DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `lookup_var reg sCopy = SOME w` by
    (qpat_assum `!x. not_fresh_at saCopy x ==> lookup_var x t = _`
       (qspec_then `reg` mp_tac) >> simp[]) >>
  qpat_assum `stmt_state_rel H ctx func c cx es sCopy`
    (strip_assume_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
  `val_wf ent.type ent.value /\ type_memory_size ent.type <= cap` by
    (qpat_assum `local_ptrs_rel func c es.scopes sCopy`
       (qspecl_then [`name`,`ent`,`reg`,`cap`] mp_tac o CONJUNCT1 o
        REWRITE_RULE [local_ptrs_rel_def]) >> simp[] >> strip_tac >> simp[]) >>
  `local_region c es.scopes sCopy name (w2n w) cap` by
    (simp[local_region_def] >> qexistsl [`ent`,`reg`,`w`] >> simp[]) >>
  Q.SUBGOAL_THEN
    `w2n w + cap <= w2n dw \/ w2n dw + capacity <= w2n w` ASSUME_TAC
  >- (qspecl_then [`func`,`c`,`es.scopes`,`sCopy`,`itemInst`,`xd`,
                    `w2n dw`,`capacity`,`name`,`w2n w`,`cap`]
        mp_tac localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
      simp[NoAsms,loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]) >>
  Q.SUBGOAL_THEN
    `w2n w + cap <= w2n dw \/ w2n dw + n <= w2n w` ASSUME_TAC
  >- (qpat_assum `w2n w + cap <= w2n dw \/ _` mp_tac >>
      qpat_assum `n <= capacity` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `mem_bytes_at (w2n w) cap t.vs_memory = mem_bytes_at (w2n w) cap sCopy.vs_memory` by
    (qpat_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _`
       (qspecl_then [`w2n w`,`cap`] MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
  `!i. w2n w <= i /\ i < w2n w + cap /\ i IN tnf.t_mem ==> i IN tnCopy.t_mem` by
    (qx_gen_tac `i` >> strip_tac >>
     `~(w2n dw <= i /\ i < w2n dw+n)` by
       (qpat_assum `w2n w + cap <= w2n dw \/ w2n dw + n <= w2n w` mp_tac >>
        qpat_assum `w2n w <= i` mp_tac >>
        qpat_assum `i < w2n w + cap` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     qpat_assum `!i. _ ==> (i IN tnf.t_mem <=> _)` (qspec_then `i` mp_tac) >> simp[]) >>
  `val_footprint ent.type ent.value <= cap` by
    (irule LESS_EQ_TRANS >> qexists_tac `type_memory_size ent.type` >>
     conj_tac >- (irule exprSimPropsTheory.val_footprint_le >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `!m. mem_agree_outside tnCopy.t_mem sCopy.vs_memory m ==>
       val_in_memory ent.type ent.value (w2n w) m` by
    (qpat_assum `!w m. lookup_var reg sCopy = SOME w /\ _ ==> _`
       (qspec_then `w` mp_tac) >> simp[]) >>
  drule_all bodyPtrBytestringBuiltinsWindowGhostTheory.robust_val_in_memory_window_transport >>
  simp[]
QED

Resume for_nonslot_array_element_prepare_full[memory_place_child]:
  Q_TAC (fn tm => SUBGOAL_THEN tm
    (qx_choose_then `initialEntry` (map_every assume_tac o CONJUNCTS)))
    `?initialEntry. lookup_scopes name em.scopes = SOME initialEntry /\
      subscripts_type initialEntry.type path = SOME (ArrayTV stv bd)`
  >- (qpat_assum `!name path. rv = PlaceR (MemoryPlace name path) ==>
                 runtime_place_typed cx em _ _`
        (qspecl_then [`name`,`path`] mp_tac) >>
      qpat_assum `rv = PlaceR (MemoryPlace name path)` (fn th => REWRITE_TAC [th]) >>
      simp[NoAsms, vyperPlaceTypingTheory.runtime_place_typed_memory]) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm
    (qx_choose_then `currentEntry` (map_every assume_tac o CONJUNCTS)))
    `?currentEntry. lookup_scopes name es.scopes = SOME currentEntry /\
      currentEntry.type = initialEntry.type /\
      evaluate_subscripts currentEntry.type currentEntry.value path =
        evaluate_subscripts initialEntry.type initialEntry.value path`
  >- (qpat_assum `loc = LocMemory ==> !name path. rv = PlaceR _ ==> OPTION_MAP _ _ = _`
        mp_tac >>
      qpat_assum `loc = LocMemory` (fn th => REWRITE_TAC [th]) >>
      disch_then (qspecl_then [`name`,`path`] mp_tac) >>
      qpat_assum `rv = PlaceR (MemoryPlace name path)` (fn th => REWRITE_TAC [th]) >>
      qpat_assum `lookup_scopes name em.scopes = SOME initialEntry`
        (fn th => REWRITE_TAC [th]) >>
      Cases_on `lookup_scopes name es.scopes` >> simp[NoAsms]) >>
  qpat_assum `expr_sim_inv c cx env es`
    (map_every assume_tac o CONJUNCTS o
     REWRITE_RULE [exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  qpat_assum `env_consistent env cx es`
    (map_every assume_tac o CONJUNCTS o
     REWRITE_RULE [vyperTypeInvariantsTheory.env_consistent_def,
                   vyperTypeInvariantsTheory.env_scopes_consistent_def]) >>
  `IS_SOME (FLOOKUP env.var_types name)` by
    (qpat_assum `!id ent. lookup_scopes id es.scopes = SOME ent ==>
                 IS_SOME (FLOOKUP env.var_types id)`
       (qspecl_then [`name`,`currentEntry`] MATCH_MP_TAC) >>
     first_assum ACCEPT_TAC) >>
  Cases_on `FLOOKUP env.var_types name`
  >- (qpat_assum `IS_SOME NONE` mp_tac >> simp[NoAsms]) >>
  rename1 `FLOOKUP env.var_types name = SOME ty` >>
  `ty = rootTy` by
    (qpat_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==>
                 c.ce_var_type id = SOME ty`
       (qspecl_then [`name`,`ty`] mp_tac) >>
     qpat_assum `FLOOKUP env.var_types name = SOME ty` (fn th => REWRITE_TAC [th]) >>
     qpat_assum `c.ce_var_type name = SOME rootTy` (fn th => simp[NoAsms,th])) >>
  `currentEntry.type = rootTV` by
    (qpat_assum `!id ty ent. FLOOKUP env.var_types id = SOME ty /\
                  lookup_scopes id es.scopes = SOME ent ==> _`
       (qspecl_then [`name`,`ty`,`currentEntry`] mp_tac) >>
     qpat_assum `FLOOKUP env.var_types name = SOME ty` (fn th => REWRITE_TAC [th]) >>
     qpat_assum `lookup_scopes name es.scopes = SOME currentEntry`
        (fn th => REWRITE_TAC [th]) >>
     qpat_assum `ty = rootTy` SUBST1_TAC >>
     qpat_assum `evaluate_type (get_tenv cx) rootTy = SOME rootTV`
        (fn th => simp[NoAsms,th])) >>
  `pathTV = ArrayTV stv bd` by
    (qpat_assum `mem_path_offset rootTV path = SOME (delta,pathTV)`
       (mp_tac o cj 1 o MATCH_MP exprSimPropsTheory.mem_path_offset_sound) >>
     qpat_assum `currentEntry.type = rootTV` (SUBST1_TAC o SYM) >>
     qpat_assum `currentEntry.type = initialEntry.type` SUBST1_TAC >>
     qpat_assum `subscripts_type initialEntry.type path = SOME (ArrayTV stv bd)`
        (fn th => simp[NoAsms,th])) >>
  suspend "memory_place_live"
QED

Resume for_nonslot_array_element_prepare_full[memory_place_live]:
  `evaluate_subscripts currentEntry.type currentEntry.value path = INL (ArrayV av)` by
    (qpat_assum `!name path. rv = PlaceR (MemoryPlace name path) ==>
       ?entry. lookup_scopes name em.scopes = SOME entry /\ _`
       (qspecl_then [`name`,`path`] mp_tac) >>
     qpat_assum `rv = PlaceR (MemoryPlace name path)` (fn th => REWRITE_TAC [th]) >>
     qpat_assum `lookup_scopes name em.scopes = SOME initialEntry`
       (fn th => REWRITE_TAC [th]) >>
     qpat_assum `evaluate_subscripts currentEntry.type currentEntry.value path = _`
       SUBST1_TAC >> simp[NoAsms]) >>
  `value_has_type currentEntry.type currentEntry.value /\
   well_formed_type_value currentEntry.type` by
    (qpat_assum `state_well_typed es`
      (assume_tac o cj 1 o REWRITE_RULE [vyperTypeInvariantsTheory.state_well_typed_def]) >>
     drule_all vyperTypeEnvTheory.scope_well_typed_lookup_scopes >> simp[]) >>
  `mem_path_offset currentEntry.type path = SOME (delta,ArrayTV stv bd)` by
    (qpat_assum `currentEntry.type = rootTV` SUBST1_TAC >>
     qpat_assum `pathTV = ArrayTV stv bd` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `xs = array_elements (ArrayTV stv bd) av` by
    (qpat_assum `extract_elements (ArrayTV stv bd) (ArrayV av) = SOME xs` mp_tac >>
     simp[NoAsms,vyperValueOperationTheory.extract_elements_def]) >>
  `k < LENGTH xs` by
    (qpat_assum `k < LENGTH vs` mp_tac >>
     qpat_assum `vs = MAP Value xs` SUBST1_TAC >>
     simp[NoAsms]) >>
  mp_tac (Q.INST
    [`es` |-> `es`, `name` |-> `name`, `entry` |-> `currentEntry`, `cenv` |-> `c`,
     `root` |-> `root`, `sz` |-> `room`, `s` |-> `sCopy`, `rw` |-> `rw`,
     `D` |-> `D`, `lo` |-> `lo`, `d` |-> `d`, `cx` |-> `cx`,
     `G` |-> `GCopy`, `tn` |-> `tnCopy`, `path` |-> `path`, `delta` |-> `delta`,
     `stv` |-> `stv`, `bd` |-> `bd`, `av` |-> `av`, `vs` |-> `xs`, `k` |-> `k`]
    for_local_place_array_current_child) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "memory_place_bounds"
QED

Resume for_nonslot_array_element_prepare_full[memory_place_bounds]:
  `?cap h. h = (case bd of Fixed _ => 0 | Dynamic _ => 32) /\
           k < cap /\ type_memory_size (ArrayTV stv bd) = h + cap * stride` by
    (qpat_assum `compatible_bound bd (LENGTH _)` mp_tac >>
     qpat_assum `k < LENGTH xs` mp_tac >>
     qpat_assum `stride = type_memory_size dtv` SUBST1_TAC >>
     qpat_assum `stv = dtv` (SUBST1_TAC o SYM) >>
     namedCases_on `bd` ["cap", "cap"] >>
     simp[NoAsms, vyperValueTheory.compatible_bound_def,
          valueEncodingTheory.type_memory_size_def] >>
     rpt strip_tac >> qexists_tac `cap` >> simp[NoAsms] >>
     qpat_assum `k < LENGTH xs` mp_tac
     >- (qpat_assum `cap = LENGTH xs` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     qpat_assum `LENGTH xs <= cap` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `h = (if dyn then 32 else 0)` by (Cases_on `bd` >> simp[]) >>
  `h + k*stride + stride <= type_memory_size (ArrayTV stv bd)` by
    (`SUC k * stride <= cap * stride` by (irule LESS_MONO_MULT >> simp[]) >>
     qpat_assum `type_memory_size (ArrayTV stv bd) = h + cap * stride` SUBST1_TAC >>
     qpat_assum `SUC k * stride <= cap * stride` (mp_tac o REWRITE_RULE [MULT_CLAUSES]) >>
     decide_tac) >>
  qpat_assum `stmt_state_rel H ctx func c cx es sCopy`
    (assume_tac o cj 1 o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
  `w2n rw + room <= sCopy.vs_alloca_next /\ type_memory_size currentEntry.type <= room` by
    (qpat_assum `local_ptrs_rel func c es.scopes sCopy`
       (qspecl_then [`name`,`currentEntry`,`root`,`room`] mp_tac o CONJUNCT1 o
        REWRITE_RULE [local_ptrs_rel_def]) >>
     qpat_assum `lookup_scopes name es.scopes = SOME currentEntry`
        (fn th => REWRITE_TAC [th]) >>
     qpat_assum `FLOOKUP c.ce_vars name = SOME (PtrVar (Var root) room)`
        (fn th => REWRITE_TAC [th]) >>
     qpat_assum `lookup_var root sCopy = SOME rw` (fn th => simp[NoAsms,th]) >>
     strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  `local_region c es.scopes sCopy name (w2n rw) room` by
    (REWRITE_TAC [local_region_def] >> qexistsl [`currentEntry`,`root`,`rw`] >>
     rpt conj_tac >> REWRITE_TAC [] >> first_assum ACCEPT_TAC) >>
  Q.SUBGOAL_THEN `w2n rw + room <= w2n dw \/ w2n dw + capacity <= w2n rw` ASSUME_TAC
  >- (qpat_assum `?inst. MEM inst (fn_insts func) /\ _`
        (qx_choose_then `site` (map_every assume_tac o CONJUNCTS)) >>
      `FLOOKUP sCopy.vs_allocas site.inst_id = SOME (w2n dw,capacity)` by
        (qpat_assum `site.inst_id = aidItem` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      qspecl_then [`func`,`c`,`es.scopes`,`sCopy`,`site`,`xd`,
                  `w2n dw`,`capacity`,`name`,`w2n rw`,`room`]
        mp_tac localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      simp[NoAsms,loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM]) >>
  `bw = rw + n2w delta` by
    (qpat_assum `eval_operand (vv_operand vv) u = SOME (rw + n2w delta)` mp_tac >>
     qpat_assum `eval_operand (vv_operand vv) u = SOME bw` (fn th => simp[NoAsms,th])) >>
  `w2n rw + delta + type_memory_size (ArrayTV stv bd) <= sCopy.vs_alloca_next` by
    (qpat_assum `w2n rw + room <= sCopy.vs_alloca_next` mp_tac >>
     qpat_assum `type_memory_size currentEntry.type <= room` mp_tac >>
     qpat_assum `delta + type_memory_size (ArrayTV stv bd) <= type_memory_size currentEntry.type`
        mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `w2n bw = w2n rw + delta` by
    (qpat_assum `bw = rw + n2w delta` SUBST1_TAC >>
     irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >>
     qpat_assum `w2n rw + delta + type_memory_size (ArrayTV stv bd) <= sCopy.vs_alloca_next` mp_tac >>
     qpat_assum `sCopy.vs_alloca_next < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qabbrev_tac `off = h + k*stride` >>
  qabbrev_tac `sz = type_memory_size (ArrayTV stv bd)` >>
  `lookup_var out sCopy = SOME (bw + n2w off)` by
    (qpat_assum `h = (if dyn then 32 else 0)` (SUBST1_TAC o SYM) >> simp[Abbr `off`]) >>
  `w2n bw + sz <= sCopy.vs_alloca_next` by
    (qpat_assum `w2n bw = w2n rw + delta` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `w2n bw + off + stride < dimword (:256)` by
    (qpat_assum `off + stride <= sz` mp_tac >>
     qpat_assum `w2n bw + sz <= sCopy.vs_alloca_next` mp_tac >>
     qpat_assum `sCopy.vs_alloca_next < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  Q.SUBGOAL_THEN
    `(stride = 0 \/ w2n bw + off + stride <= sCopy.vs_alloca_next) /\
     (w2n bw + off + stride <= w2n dw \/ w2n dw + stride <= w2n bw + off)`
    (map_every assume_tac o CONJUNCTS)
  >- (qpat_assum `w2n rw + room <= w2n dw \/ w2n dw + capacity <= w2n rw` mp_tac >>
      qpat_assum `w2n bw = w2n rw + delta` mp_tac >>
      qpat_assum `w2n bw + sz <= sCopy.vs_alloca_next` mp_tac >>
      qpat_assum `off + stride <= sz` mp_tac >>
      qpat_assum `delta + sz <= type_memory_size currentEntry.type` mp_tac >>
      qpat_assum `type_memory_size currentEntry.type <= room` mp_tac >>
      qpat_assum `stride = type_memory_size dtv` mp_tac >>
      qpat_assum `capacity = type_memory_size dtv` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `w2n (bw + n2w off) = w2n bw + off` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >>
     qpat_assum `w2n bw + off + stride < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qabbrev_tac `v = EL k xs` >>
  `EL k vs = Value v` by
    (qpat_assum `vs = MAP Value xs` SUBST1_TAC >>
     qpat_assum `Abbrev (v = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `k < LENGTH xs` (fn th => simp[NoAsms,EL_MAP,th])) >>
  `!mem. mem_agree_outside tnCopy.t_mem sCopy.vs_memory mem ==>
     val_in_memory stv v (w2n bw + off) mem` by
    (qpat_assum `!mem. mem_agree_outside tnCopy.t_mem sCopy.vs_memory mem ==>
                     val_in_memory stv v _ mem` mp_tac >>
     qpat_assum `w2n bw = w2n rw + delta` SUBST1_TAC >>
     qpat_assum `h = (case bd of Fixed _ => 0 | Dynamic _ => 32)` (SUBST1_TAC o SYM) >>
     qpat_assum `stv = dtv` (fn ty =>
       qpat_assum `stride = type_memory_size dtv` (fn size =>
         simp[NoAsms, Abbr `off`,ty,size,AC ADD_ASSOC ADD_COMM]))) >>
  `0 < stride ==> ptr_covers GCopy tnCopy out sCopy stride` by suspend "memory_place_cover" >>
  qexistsl [`v`,`bw + n2w off`] >>
  qpat_assum `w2n (bw + n2w off) = w2n bw + off` (fn th => REWRITE_TAC [th]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_nonslot_array_element_prepare_full[memory_place_cover]:
  disch_tac >>
  `sz <> 0` by
    (qpat_assum `0 < stride` mp_tac >>
     qpat_assum `off + stride <= sz` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `p.ptr_location = LocMemory` by
    (qpat_assum `loc = (case vv_location vv of NONE => LocMemory | SOME l => l)` mp_tac >>
     qpat_assum `vv = LocatedValue ann p` SUBST1_TAC >>
     qpat_assum `loc = LocMemory` SUBST1_TAC >>
     simp[NoAsms,contextTheory.vv_location_def]) >>
  `ptr_mem_ok cx (post_value_type c e) (ArrayV av) (vv_operand vv) Gu tu u` by
    (qpat_assum `vv = LocatedValue ann p` SUBST1_TAC >>
     REWRITE_TAC [contextTheory.vv_operand_def] >>
     qpat_assum `vv = LocatedValue ann p` (fn loc_vv =>
       qpat_assum `ptr_vv_ok _ _ rv vv em Gu tu u`
         (mp_tac o cj 3 o REWRITE_RULE [loc_vv,bodyPtrDefsTheory.ptr_vv_ok_def])) >>
     qpat_assum `p.ptr_location = LocMemory` (fn th => REWRITE_TAC [th]) >>
     qpat_assum `read_result cx rv em = _` (fn th => simp[NoAsms,th])) >>
  `val_footprint (ArrayTV stv bd) (ArrayV av) = sz` by
    simp[Abbr `sz`, loweringPostsTheory.val_footprint_def] >>
  qpat_assum `ptr_mem_ok _ _ _ _ Gu tu u`
    (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_mem_ok_def]) >>
  disch_then (qspecl_then [`ArrayTV stv bd`,`bw`] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o cj 2) >>
  impl_tac >-
    (qpat_assum `val_footprint (ArrayTV stv bd) (ArrayV av) = sz` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (sz = _)` (fn th =>
    simp[NoAsms,exprSimPropsTheory.val_store_size_def,
         SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  disch_then (qx_choosel_then [`x`,`b`,`len`] (map_every assume_tac o CONJUNCTS)) >>
  `FLOOKUP GCopy out = FLOOKUP Gu x` by
    (qpat_assum `op_prov GCopy (Var out) = op_prov G (vv_operand vv)` mp_tac >>
     qpat_assum `op_prov G (vv_operand vv) = op_prov Gu (vv_operand vv)` SUBST1_TAC >>
     qpat_assum `vv_operand vv = Var x` SUBST1_TAC >>
     simp[NoAsms,ptrDisciplineTheory.op_prov_def]) >>
  simp[NoAsms, bodyPtrDefsTheory.ptr_covers_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`bw + n2w off`,`b`,`len`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `FLOOKUP GCopy out = FLOOKUP Gu x` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `w2n (bw + n2w off) = w2n bw + off` SUBST1_TAC >>
  conj_tac
  >- (qpat_assum `b <= w2n bw` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qpat_assum `sz + w2n bw <= b + len` mp_tac >>
  qpat_assum `off + stride <= sz` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> decide_tac
QED

Finalise for_nonslot_array_element_prepare_full
