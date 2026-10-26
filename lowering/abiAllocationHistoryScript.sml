(* Allocation records are justified by instructions that have actually run.
   TOP-LEVEL: abi_alloca_history_sequence preserves partial allocation history
   through actual successful execution; fresh sites need no runtime entry. *)
Theory abiAllocationHistory
Ancestors
  venomExecSemantics venomExecProps venomMemProofs venomState venomInst
  exprLoweringProps finite_map list relation words

Definition abi_alloca_history_def:
  abi_alloca_history code s <=>
    !id off sz. FLOOKUP s.vs_allocas id = SOME (off,sz) ==>
      ?inst n. MEM inst code /\ inst.inst_id = id /\
        inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit n] /\
        sz = w2n n
End

Theorem abi_alloca_history_empty:
  s.vs_allocas = FEMPTY ==> abi_alloca_history code s
Proof
  simp[abi_alloca_history_def]
QED

Theorem abi_alloca_history_frame:
  abi_alloca_history code s /\ t.vs_allocas = s.vs_allocas ==>
  abi_alloca_history code t
Proof
  simp[abi_alloca_history_def]
QED

Theorem abi_alloca_history_alloca:
  abi_alloca_history code s /\ MEM inst code /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit n] /\
  exec_alloca inst s n = OK t ==>
  abi_alloca_history code t
Proof
  simp[exec_alloca_def, AllCaseEqs(), LET_THM] >> rpt strip_tac >>
  gvs[abi_alloca_history_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem abi_alloca_history_non_alloca:
  abi_alloca_history code s /\ step_inst_base inst s = OK t /\
  inst.inst_opcode <> ALLOCA ==> abi_alloca_history code t
Proof
  strip_tac >> drule step_inst_base_OK_not_INVOKE >> strip_tac >>
  mp_tac (Q.SPECL [`inst`, `s`, `t`] step_inst_base_preserves_alloca_fields) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all abi_alloca_history_frame >> simp[]
QED

Theorem abi_alloca_history_step:
  abi_alloca_history code s /\ MEM inst code /\
  step_inst_base inst s = OK t ==> abi_alloca_history code t
Proof
  Cases_on `inst.inst_opcode = ALLOCA` >> strip_tac
  >- (qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
      asm_simp_tac (srw_ss()) [Once step_inst_base_def, AllCaseEqs()] >>
      strip_tac >> gvs[] >> drule_all abi_alloca_history_alloca >> simp[]) >>
  drule_all abi_alloca_history_non_alloca >> simp[]
QED

Theorem abi_alloca_history_sequence:
  !insts s t code.
  run_inst_seq insts s = OK t /\ abi_alloca_history code s /\
  (!inst. MEM inst insts ==> MEM inst code) ==>
  abi_alloca_history code t
Proof
  Induct_on `insts` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> rename1 `run_inst_seq (inst::rest) initial = OK final` >>
  simp_tac bool_ss [Once run_inst_seq_def] >>
  Cases_on `step_inst_base inst initial` >> simp[] >> strip_tac >>
  rename1 `step_inst_base inst initial = OK middle` >>
  `abi_alloca_history code middle` by
    (irule abi_alloca_history_step >> qexistsl_tac [`inst`, `initial`] >>
     simp[]) >>
  first_x_assum (qspecl_then [`middle`, `final`, `code`] mp_tac) >>
  simp[]
QED

Theorem abi_alloca_history_reachable:
  !s t. RTC (\s t. ?inst. MEM inst code /\ step_inst_base inst s = OK t) s t ==>
    abi_alloca_history code s ==> abi_alloca_history code t
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac >>
  drule_all abi_alloca_history_step >> strip_tac >>
  first_x_assum irule >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ALLOCATION_HISTORY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI allocation history not kernel closed: " ^ n)
  end) (DB.thms "abiAllocationHistory");

