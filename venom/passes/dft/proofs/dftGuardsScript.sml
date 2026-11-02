(* Runtime guards used by DFT instruction swaps. *)
Theory dftGuards
Ancestors
  venomState venomExecSemantics venomWf venomEffects venomInst finite_map list
  dftCommutation

Theorem dft_operand_defined:
  (!v. MEM (Var v) ops ==> v IN FDOM s.vs_vars) /\
  (!l. MEM (Label l) ops ==> l IN FDOM s.vs_labels) ==>
  !op. MEM op ops ==> ?w. eval_operand op s = SOME w
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def] >>
  simp[FLOOKUP_DEF] >> metis_tac[]
QED

Theorem dft_exec_pure1_total:
  LENGTH inst.inst_operands = 1 /\ LENGTH inst.inst_outputs = 1 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_pure1 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  gvs[exec_pure1_def]
QED

Theorem dft_exec_pure2_total:
  LENGTH inst.inst_operands = 2 /\ LENGTH inst.inst_outputs = 1 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_pure2 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = [op1; op2]` >>
  `?v1. eval_operand op1 s = SOME v1` by metis_tac[] >>
  `?v2. eval_operand op2 s = SOME v2` by metis_tac[] >>
  simp[exec_pure2_def]
QED

Theorem dft_exec_pure3_total:
  LENGTH inst.inst_operands = 3 /\ LENGTH inst.inst_outputs = 1 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_pure3 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = [op1; op2; op3]` >>
  `?v1. eval_operand op1 s = SOME v1` by metis_tac[] >>
  `?v2. eval_operand op2 s = SOME v2` by metis_tac[] >>
  `?v3. eval_operand op3 s = SOME v3` by metis_tac[] >>
  simp[exec_pure3_def]
QED

Theorem dft_exec_read0_total:
  LENGTH inst.inst_outputs = 1 ==> ?t. exec_read0 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> simp[exec_read0_def]
QED

Theorem dft_exec_read1_total:
  LENGTH inst.inst_operands = 1 /\ LENGTH inst.inst_outputs = 1 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_read1 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >>
  gvs[exec_read1_def]
QED

Theorem dft_exec_write2_total:
  LENGTH inst.inst_operands = 2 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_write2 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = [op1; op2]` >>
  `?v1. eval_operand op1 s = SOME v1` by metis_tac[] >>
  `?v2. eval_operand op2 s = SOME v2` by metis_tac[] >>
  simp[exec_write2_def]
QED

Definition dft_runtime_error_opcode_def:
  dft_runtime_error_opcode op <=> MEM op [DELEGATECALL; CREATE; CREATE2]
End

Theorem dft_runtime_error_all_read:
  dft_runtime_error_opcode op ==> read_effects op = all_effects
Proof
  simp[dft_runtime_error_opcode_def] >> rpt strip_tac >>
  gvs[read_effects_def]
QED

Theorem dft_exec_ext_call_total:
  LENGTH inst.inst_outputs = 1 ==>
  ?t. exec_ext_call inst s gas addr value ao az ro rz static = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> strip_tac >>
  simp[exec_ext_call_def] >> pairarg_tac >> simp[]
QED

Theorem dft_eval_operands_defined:
  !ops. (!op. MEM op ops ==> ?v. eval_operand op s = SOME v) ==>
        ?vs. eval_operands ops s = SOME vs
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

(* Select the opcode argument without traversing unselected semantic branches. *)
fun dft_opcode_dispatch_conv th tm =
  let
    val (_, args) = strip_comb tm
    val lhs = lhs (concl th)
    fun locate _ [] = raise Fail "opcode scrutinee absent"
      | locate k (a::rest) = if aconv a lhs then k else locate (k+1) rest
    val k = locate 0 args
    fun focus 0 = RAND_CONV (REWR_CONV th)
      | focus n = RATOR_CONV (focus (n-1))
  in
    (focus (length args - 1 - k) THENC
     FIRST_CONV (map REWR_CONV (CONJUNCTS opcode_case_def))) tm
  end;

Theorem dft_guarded_nofail_total:
  inst_wf inst /\ ~is_pseudo inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> ALLOCA /\
  opcode_fail_class inst.inst_opcode = NoFail /\
  ~dft_runtime_error_opcode inst.inst_opcode /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v)
  ==> ?t. step_inst fuel C inst s = OK t
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode` >>
  fs[is_pseudo_def, is_terminator_def, opcode_fail_class_def,
     dft_runtime_error_opcode_def] >>
  fs[inst_wf_def] >>
  simp[Once step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_x_assum `inst.inst_opcode = _`
    (fn th => CONV_TAC (BINDER_CONV (LHS_CONV (dft_opcode_dispatch_conv th)))) >>
  all_tac
  >>~- ([`exec_pure1 _ _ _`], irule dft_exec_pure1_total >> simp[])
  >>~- ([`exec_pure2 _ _ _`], irule dft_exec_pure2_total >> simp[])
  >>~- ([`exec_pure3 _ _ _`], irule dft_exec_pure3_total >> simp[])
  >>~- ([`exec_read0 _ _ _`], irule dft_exec_read0_total >> simp[])
  >>~- ([`exec_read1 _ _ _`], irule dft_exec_read1_total >> simp[])
  >>~- ([`exec_write2 _ _ _`], irule dft_exec_write2_total >> simp[])
  >>~- ([`eval_operands _ _`], suspend "log_total") >>
  gvs[LENGTH_EQ_NUM_compute, DISJ_IMP_THM, FORALL_AND_THM]
  >>~- ([`exec_ext_call _ _ _ _ _ _ _ _ _ _`],
         irule dft_exec_ext_call_total >> simp[])
QED

Resume dft_guarded_nofail_total[log_total]:
  `MEM (EL 0 (REVERSE rest)) rest /\ MEM (EL 1 (REVERSE rest)) rest` by
    (conj_tac >> once_rewrite_tac[GSYM MEM_REVERSE] >>
     irule EL_MEM >> simp[]) >>
  `?off. eval_operand (EL 0 (REVERSE rest)) s = SOME off` by metis_tac[MEM] >>
  `?sz. eval_operand (EL 1 (REVERSE rest)) s = SOME sz` by metis_tac[MEM] >>
  `?topics. eval_operands (DROP 2 (REVERSE rest)) s = SOME topics` by
    (irule dft_eval_operands_defined >> rpt strip_tac >>
     drule rich_listTheory.MEM_DROP_IMP >> simp[] >> strip_tac >> metis_tac[MEM]) >>
  fs[]
QED

Finalise dft_guarded_nofail_total

Theorem dft_empty_write_ok_updates:
  ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> ALLOCA /\
  write_effects inst.inst_opcode = empty_effects /\
  step_inst fuel C inst s = OK t ==>
  ?updates.
    EVERY (\p. MEM (FST p) inst.inst_outputs) updates /\
    t = FOLDL (\u p. update_var (FST p) (SND p) u) s updates
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  fs[is_pseudo_def, is_terminator_def, write_effects_def,
     empty_effects_def, all_effects_def] >>
  fs[Once step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `inst.inst_opcode = _`
    (fn th => CONV_TAC (LAND_CONV (LHS_CONV (dft_opcode_dispatch_conv th)))) >>
  gvs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
  >>~- ([`EVERY (\p. FST p = out) _`],
    qmatch_goalsub_abbrev_tac `update_var out value s` >>
    qexists_tac `[(out,value)]` >> simp[])
  >>~- ([`inst.inst_opcode = BUMP`],
    qexists_tac `[(ptr_out,base_val); (next_out,base_val + sz)]` >> simp[])
  >> qexists_tac `[]` >> simp[]
QED

Theorem dft_update_var_error_iff[local]:
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs ==>
  (step_inst fuel C inst (update_var v w s) = Error e <=>
   step_inst fuel C inst s = Error e)
Proof
  strip_tac >>
  `!y. MEM (Var y) inst.inst_operands ==> v <> y` by metis_tac[] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all step_inst_invoke_frame >>
      disch_then (qspecl_then [`fuel`,`C`,`s`,`w`] mp_tac) >>
      Cases_on `step_inst fuel C inst s` >> simp[]) >>
  drule_all step_inst_frame >>
  disch_then (qspecl_then [`fuel`,`C`,`s`,`w`] mp_tac) >>
  Cases_on `step_inst fuel C inst s` >> simp[map_result_state_def]
QED

Theorem dft_output_updates_error_iff[local]:
  !updates s.
    EVERY (\p. ~MEM (Var (FST p)) inst.inst_operands /\
                ~MEM (FST p) inst.inst_outputs) updates ==>
    (step_inst fuel C inst
       (FOLDL (\u p. update_var (FST p) (SND p) u) s updates) = Error e <=>
     step_inst fuel C inst s = Error e)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[dft_update_var_error_iff]
QED

Theorem dft_empty_write_error_iff:
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ write_effects x.inst_opcode = empty_effects /\
  step_inst fuel C x s = OK t /\
  (!v. MEM v x.inst_outputs ==>
       ~MEM (Var v) y.inst_operands /\ ~MEM v y.inst_outputs) ==>
  (step_inst fuel C y t = Error e <=> step_inst fuel C y s = Error e)
Proof
  strip_tac >> drule_all dft_empty_write_ok_updates >> strip_tac >>
  gvs[] >> irule dft_output_updates_error_iff >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem dft_all_read_independent_empty_write:
  read_effects y.inst_opcode = all_effects /\
  effects_independent x.inst_opcode y.inst_opcode ==>
  write_effects x.inst_opcode = empty_effects
Proof
  strip_tac >> gvs[effects_independent_def] >>
  Cases_on `x.inst_opcode` >>
  gvs[write_effects_def, all_effects_def, empty_effects_def]
QED
