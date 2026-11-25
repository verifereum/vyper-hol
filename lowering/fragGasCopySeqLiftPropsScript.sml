(* Lift a checked copy sequence to a zero-mark origin and pointer path. *)
Theory fragGasCopySeqLiftProps
Ancestors
  ptrSafetyTransport fragGasSeqPtr fragGasOriginPtr exprLoweringProps fragExecMem fragExec
  ptrDiscipline unitTransformDefs venomMemProps venomState venomExecSemantics
  venomExecProofs venomInst rich_list list pred_set

Theorem inst_seq_ptr_lower_bound_transport:
  !code s G tn G' tn'.
    lo0 <= lo /\ allocas_from lo s /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code /\
    inst_seq_ptr D lo0 ctx fn PG G tn code s G' tn' ==>
    inst_seq_ptr D lo ctx fn PG G tn code s G' tn'
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac >>
  conj_tac >- (irule ptr_inst_ok_lower_bound_transport >> metis_tac[]) >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  first_x_assum irule >> simp[] >>
  `u.vs_allocas = s.vs_allocas` by
    metis_tac[venomMemPropsTheory.step_inst_base_preserves_allocas] >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Theorem run_inst_seq_allocas_from[local]:
  !code s t.
    allocas_from lo s /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code /\
    run_inst_seq code s = OK t ==>
    allocas_from lo t
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  first_x_assum irule >> simp[] >> qexists_tac `u` >> simp[] >>
  `u.vs_allocas = s.vs_allocas` by
    metis_tac[venomMemPropsTheory.step_inst_base_preserves_allocas] >>
  gvs[allocas_from_def] >> metis_tac[]
QED

(* A checked straight-line run without GAS, ALLOCA or calls, checked at the
   reserved bound 0, is a zero-mark joint path at any bound lo below every
   ALLOCA site. *)
Theorem run_inst_seq_origin_ptr_lift:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code /\
  run_inst_seq_mem_ok code s /\
  (ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post u. code = pre ++ i::post /\
      run_inst_seq pre s = OK u ==>
      unitTransformDefs$dalloca_no_wrap i u) /\
  allocas_from lo s /\
  inst_seq_ptr D 0 ctx func PG G tn code s G' tn' /\
  run_inst_seq code s = OK t ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code),G',tn') /\
  allocas_from lo t
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    fs[EVERY_MEM] >>
  reverse conj_tac >- metis_tac[run_inst_seq_allocas_from] >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM]) >>
  `inst_seq_ptr D lo ctx func PG G tn code s G' tn'` by
    (irule inst_seq_ptr_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn)
     (MAP (\i. (func.fn_name, i.inst_id) IN explicit)
        (FILTER (\i. i.inst_opcode = GAS) code))
     (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code),G',tn')` by
    (irule run_inst_seq_gas_origin_ptr_path >> metis_tac[]) >>
  gvs[]
QED
