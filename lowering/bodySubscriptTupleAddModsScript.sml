(* The tuple address calculation has one machine/ghost endpoint for all horizons. *)
Theory bodySubscriptTupleAddMods
Ancestors
  bodyFullAttributeAdd bodyMakeSlotVvFrameMods bodyForRangeScalarFrameMods
  bodyPtrMakeArrayEmission bodyFullUnwrapRun bodyFullPostsMods
  exprSimTuple exprSimAttributeProps exprSimUnwrap exprOperandVar
  fragExec emitHelperProps freshWrites allocaHistory ptrDiscipline
  context compileEnv venomState venomInst ASCIInumbers finite_map

Triviality tuple_add_history:
  alloca_history func s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode <> ALLOCA /\
  t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb /\
  t.vs_inst_idx = SUC s.vs_inst_idx ==>
  alloca_history func t
Proof
  simp[alloca_history_def] >> strip_tac >> rpt strip_tac >> gvs[] >>
  `k < s.vs_inst_idx \/ k = s.vs_inst_idx` by decide_tac
  >- (first_x_assum irule >> simp[] >> goal_assum drule >> simp[])
  >> gvs[]
QED

Theorem tuple_subscript_add_endpoint_mods:
  compile_expr cenv ty obj sa = (bvv,sm) /\
  off = tuple_offset cenv tys (vv_loc bvv) k /\
  emit_op ADD [vv_operand bvv; Lit (n2w off)] sm = (p,sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  eval_operand (vv_operand bvv) s = SOME w /\ op_taint tn1 (vv_operand bvv) = {} /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post_mods H ctx func cenv cx obj es sa sm s0 ee raw bvv s /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 s) ==>
  ?out i u t G2 tn2.
    p = Var out /\ out = STRING #"%" (toString sm.cs_next_var) /\
    i = mk_inst sm.cs_next_id ADD [vv_operand bvv; Lit (n2w off)] [out] /\
    u = update_var out (w + n2w off) s /\
    t = (u with vs_inst_idx := SUC s.vs_inst_idx) /\
    G2 = step_prov PG G1 i u /\ tn2 = step_taint i s u tn1 /\
    emitted_insts sm sb = [i] /\ sm.cs_next_id < sb.cs_next_id /\
    (!D lo' explicit. allocas_from lo' s ==>
      gas_origin_ptr_path (D,lo',explicit,ctx,func,PG) (s,G1,tn1) [] (OK t,G2,tn2)) /\
    eval_operand (vv_operand bvv) t = SOME w /\ eval_operand p t = SOME (w + n2w off) /\
    FLOOKUP G2 out = op_prov G1 (vv_operand bvv) /\ op_taint tn2 p = {} /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G2 x = FLOOKUP G1 x /\ op_taint tn2 (Var x) = op_taint tn1 (Var x)) /\
    tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
    tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2 /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post_mods H ctx func cenv cx obj es sa sb s0 ee raw bvv t /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 t)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac emit_op_fetch_boundary >>
  qpat_x_assum `tmp = STRING _ _` SUBST_ALL_TAC >>
  drule_then strip_assume_tac emitted_insts_emit_op >>
  drule_then strip_assume_tac compile_expr_extends >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ADD [vv_operand bvv; Lit (n2w off)]
    [STRING #"%" (toString sm.cs_next_var)]` >>
  qabbrev_tac `u = update_var (STRING #"%" (toString sm.cs_next_var)) (w + n2w off) s` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G2 = step_prov PG G1 i u` >>
  qabbrev_tac `tn2 = step_taint i s u tn1` >>
  `(!D lo' explicit. allocas_from lo' s ==>
     gas_origin_ptr_path (D,lo',explicit,ctx,func,PG) (s,G1,tn1) [] (OK t,G2,tn2)) /\
   FLOOKUP G2 (STRING #"%" (toString sm.cs_next_var)) = op_prov G1 (vv_operand bvv) /\
   op_taint tn2 p = {} /\
   tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
   tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
   (!x. x <> STRING #"%" (toString sm.cs_next_var) ==>
      FLOOKUP G2 x = FLOOKUP G1 x /\
      op_taint tn2 (Var x) = op_taint tn1 (Var x))` by
    (map_every (fn tm => qpat_assum tm
       (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (i = _)`,`Abbrev (u = _)`,`Abbrev (t = _)`,
        `Abbrev (G2 = _)`,`Abbrev (tn2 = _)`] >>
     drule_all (SIMP_RULE bool_ss [] (Q.INST
       [`out` |-> `STRING #"%" (toString sm.cs_next_var)`] attribute_add_full_frame)) >>
     disch_then (mp_tac o CONJUNCT2) >>
     simp[arithmeticTheory.ADD1, Abbr `t`, Abbr `G2`, Abbr `tn2`, Abbr `u`, Abbr `i`]) >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> x <> STRING _ _` (drule_then assume_tac) >>
     simp[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `eval_operand (vv_operand bvv) t = SOME w` by
    (`!x. vv_operand bvv = Var x ==> not_fresh_at sm x` by
       (drule (cj 1 compiler_compile_var) >> simp[]) >>
     Cases_on `vv_operand bvv` >> fs[eval_operand_def] >>
     simp[Abbr `t`, Abbr `u`, update_var_def, eval_operand_def]) >>
  `alloca_history func t` by
    (irule tuple_add_history >> qexistsl [`bb`,`i`,`s`] >>
     simp[Abbr `i`, Abbr `t`, Abbr `u`, update_var_def, mk_inst_def]) >>
  qexistsl [`STRING #"%" (toString sm.cs_next_var)`,`i`,`u`,`t`,`G2`,`tn2`] >>
  suspend "assemble"
QED

Resume tuple_subscript_add_endpoint_mods[assemble]:
  simp[] >> rpt conj_tac
  >- simp[Abbr `t`, Abbr `u`, eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
  >- simp[Abbr `t`, Abbr `u`, update_var_def]
  >- simp[Abbr `t`, Abbr `u`, update_var_def]
  >- simp[Abbr `t`, Abbr `u`, update_var_def]
  >- simp[Abbr `t`, arithmeticTheory.ADD1]
  >- (strip_tac >> fs[Abbr `t`, Abbr `u`, update_var_def, allocas_below_fmp_def] >>
      first_assum ACCEPT_TAC)
  >- simp[Abbr `t`, Abbr `u`, update_var_def]
  >- simp[Abbr `t`, Abbr `u`, update_var_def]
  >- (irule ghost_kept_at_clean_suffix >> qexistsl [`G1`,`tn1`] >>
      simp[] >> rpt strip_tac >> first_x_assum drule >> simp[] >> first_x_assum drule >> simp[])
  >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac
  >- (irule make_slot_vv_readonly_post_mods >> simp[] >> qexistsl [`s`,`sm`] >>
      simp[Abbr `t`, Abbr `u`, update_var_def])
  >> irule ghost_inv_at_mods_exterior_frame >> qexistsl [`G1`,`ee`,`s`,`sa`,`tn1`] >>
  simp[Abbr `t`, Abbr `u`, update_var_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> first_x_assum drule >> simp[]
QED

Finalise tuple_subscript_add_endpoint_mods
