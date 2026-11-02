(* Runtime guards used by DFT instruction swaps. *)
Theory dftGuards
Ancestors
  venomState venomExecSemantics venomWf venomEffects venomInst finite_map list

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
