Theory bodyPtrAttributeAdd
Ancestors
  bodyPtrDefs typedCopyPtr decoderGhostFramePtr fragGasSeqPtr emitHelperProps exprSimAttribute
  fragExec fragGasPathPtr compileEnv emitHelper context venomInst venomState venomExecSemantics
  ptrSafeRun ptrDiscipline list arithmetic finite_map words

(* A checked emitted instruction is a counted edge, not merely an erased
   execution.  This interface also covers other pure emitted opcodes. *)
Theorem attribute_emit_op_path_ptr:
  emit_op opc args sa = (op, sb) /\ fn_has_code sa sb func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!out. step_inst_base (mk_inst sa.cs_next_id opc args [out]) s =
         OK (update_var out w s)) /\
  (!out. ptr_inst_ok D lo 0 ctx func G tn
         (mk_inst sa.cs_next_id opc args [out]) s) ==>
  gas_path_ptr D lo ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id opc args
      [STRING #"%" (toString sa.cs_next_var)])
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s))
    (step_taint (mk_inst sa.cs_next_id opc args
      [STRING #"%" (toString sa.cs_next_var)]) s
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) tn)
    (OK ((update_var (STRING #"%" (toString sa.cs_next_var)) w s)
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id opc args
      [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qmatch_goalsub_abbrev_tac `step_prov PG G inst u` >>
  `gas_path_ptr_edge D lo ctx func PG G tn s 0
     (step_prov PG G inst u) (step_taint inst s u tn)
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (straight_line_ptr_edge |> Q.INST [`i` |-> `inst`, `fn` |-> `func`]) >>
     simp[Abbr `inst`, Abbr `u`, mk_inst_def] >>
     disch_then irule >> simp[]) >>
  unabbrev_all_tac >>
  `~(update_var (STRING #"%" (toString sa.cs_next_var)) w s
       with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
    simp[update_var_def] >>
  drule (cj 1 gas_path_ptr_rules) >> strip_tac >>
  metis_tac[cj 2 gas_path_ptr_rules, ADD_CLAUSES]
QED

Theorem attribute_emit_binop_path_ptr:
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  emit_op opc [left;right] sa = (dst,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  ?out G' tn' t.
    dst = Var out /\ gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    t = (update_var out (f a b) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    G' = step_prov PG G (mk_inst sa.cs_next_id opc [left;right] [out])
           (update_var out (f a b) s) /\
    tn' = step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
           (update_var out (f a b) s) tn /\
    tn'.t_imm = tn.t_imm /\
    op_taint tn' (Var out) = {} /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `STRING #"%" (toString sa.cs_next_var)` >>
  simp[IgnAsm `s.vs_inst_idx = _`] >> rpt (irule_at Any EQ_REFL) >>
  conj_tac
  >- (`!out. step_inst_base (mk_inst sa.cs_next_id opc [left;right] [out]) s =
          OK (update_var out (f a b) s)` by
        (gen_tac >> qpat_x_assum `_ /\ _ \/ _ /\ _` strip_assume_tac >> gvs[] >>
         PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
         pure_rewrite_tac[mk_inst_def, instruction_accessors,
           instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
         simp[exec_pure2_def]) >>
      `!out. ptr_inst_ok D 0 0 ctx func G tn
         (mk_inst sa.cs_next_id opc [left;right] [out]) s` by
        (gen_tac >> match_mp_tac typedCopyPtrTheory.ptr_inst_ok_copy_len_binop >>
         metis_tac[]) >>
      irule attribute_emit_op_path_ptr >> simp[] >>
      qpat_x_assum `_ /\ _ \/ _ /\ _` strip_assume_tac >> gvs[is_terminator_def]) >>
  conj_tac
  >- (irule (cj 3 step_taint_nonmemory_frame) >>
      qpat_x_assum `_ /\ _ \/ _ /\ _` strip_assume_tac >>
      gvs[mk_inst_def]) >>
  match_mp_tac typedCopyPtrTheory.copy_len_binop_ghost_frame >> metis_tac[]
QED

(* The frame predicate only observes older variables and memory taint. *)
Theorem attribute_ghost_kept_frame:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  tn'.t_mem = tn.t_mem /\
  (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
     op_taint tn' (Var p) = op_taint tn (Var p)) ==>
  ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  simp[ghost_kept_def] >> metis_tac[]
QED

(* A fresh-variable update preserves each protected pointer. *)
Theorem attribute_ptr_covers_update:
  ptr_covers G tn p s sz /\ p <> out /\
  FLOOKUP G' p = FLOOKUP G p /\
  op_taint tn' (Var p) = op_taint tn (Var p) ==>
  ptr_covers G' tn' p
    (update_var out w s with vs_inst_idx := n) sz
Proof
  simp[ptr_covers_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem attribute_ghost_inv_update:
  ghost_inv d cenv cx es G tn s /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     p <> out) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
     op_taint tn' (Var p) = op_taint tn (Var p)) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm ==>
  ghost_inv d cenv cx es G' tn'
    (update_var out w s with vs_inst_idx := n)
Proof
  strip_tac >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_inv_def, stor_taint_ok_def, update_var_def] >>
  strip_tac >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p <> out` by metis_tac[] >>
      qpat_x_assum `!name entry p sz. _`
        (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
      simp[] >> strip_tac >>
      `FLOOKUP G' p = FLOOKUP G p /\
       op_taint tn' (Var p) = op_taint tn (Var p)` by metis_tac[] >>
      gvs[ptr_covers_def, lookup_var_def, FLOOKUP_UPDATE])
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >>
      PairCases_on `x` >> simp[return_buf_ptr_def] >>
      gvs[return_buf_ptr_def] >>
      rename1 `cenv.ce_return_buf = SOME (PtrVar (Var p) sz)` >>
      `p <> out` by metis_tac[] >>
      `FLOOKUP G' p = FLOOKUP G p /\
       op_taint tn' (Var p) = op_taint tn (Var p)` by metis_tac[] >>
      gvs[ptr_covers_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  metis_tac[]
QED

Theorem attribute_add_provenance:
  FLOOKUP
    (step_prov PG G (mk_inst id ADD [left;Lit off] [out]) t) out =
  op_prov G left
Proof
  Cases_on `left` >> Cases_on `op_prov G (Var s)` >>
  simp[step_prov_def, out_prov_def, first_prov_def, op_prov_def,
       set_prov_def, mk_inst_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED
