(*
 * The asm-to-EVM half of S7g's surplus bound, for any assembly program:
 * a frame related to an assembly state whose run is bounded (N steps,
 * memory below H) keeps D gas after each step,
 * given g gas, where g depends only on H, N and D.
 *
 * TOP-LEVEL:
 *   asm_frame_gas_surplus - the bound, generic in the program
 *)

Theory asmFrameSurplus
Ancestors
  asmFrameRun asmFrameGas asmFrameLocalStep asmFrameCallStep frameStep
  asmRunBounded asmFrameRel frameGas asmSem asmWf asmEncodeParse codegenRel
  symbolResolve vfmExecution vfmExecutionProp vfmOperation vfmContext
  callTrace list finite_map relation arithmetic

Theorem asm_frame_current_gas[local]:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a e /\
  a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
  asm_inst_gas_ok H (EL a.as_pc prog) a.as_stack /\
  frame_op_gas H + 64 * D <= frame_gas_left e /\ frame_inst_at e e op /\
  step_inst op e = (r,s') /\ LENGTH s'.contexts = LENGTH e.contexts ==>
  r <> INR (SOME OutOfGas) /\ D <= frame_gas_left s'
Proof
  strip_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a e` by fs[asm_frame_rel_def] >>
  drule_all asm_frame_decode_setup >> strip_tac >>
  `op = op'` by
    (irule frame_inst_at_unique >> qexistsl_tac [`e`, `e`] >>
     simp[] >> irule frame_inst_at_self >> simp[]) >>
  `frame_op_gas H <= frame_gas_left e` by decide_tac >>
  `D <= (frame_gas_left e - frame_op_gas H) DIV 64` by
    (simp[X_LE_DIV] >> decide_tac) >>
  drule_all asm_frame_gas_step >> strip_tac >>
  qpat_x_assum `!op r s'. _` (qspecl_then [`op`, `r`, `s'`] mp_tac) >>
  gvs[] >> rw[] >> decide_tac
QED

(* Why it should hold.  Induction on N along the frame's own states:
   asm_frame_step steps the assembly and the frame together
   (frame_reaches_next / frame_reaches_last place every frame state of
   frame_inst_at on that chain), asm_run_bounded supplies each step's
   side conditions through the terminal step, and
   asm_frame_gas_step bounds each step's cost by frame_op_gas H, with a
   call or create leaving at least (gas - frame_op_gas H) DIV 64.  So
   g = G N with G 0 = frame_op_gas H + 64 * D and
   G (SUC k) = 64 * G k + frame_op_gas H + 64 * D. The 64 * D
   covers a call or CREATE whose own step keeps a 64th. *)
Theorem asm_frame_gas_surplus:
  !H N D. ?g. !prog data es0 a e s op r s'.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a e /\
    wf_state e /\ g <= frame_gas_left e /\
    asm_run_bounded (SND (compute_label_offsets prog))
      (build_offset_to_pc prog) prog H N a /\
    frame_inst_at e s op /\
    step_inst op s = (r, s') /\ LENGTH s'.contexts = LENGTH s.contexts
    ==>
    r <> INR (SOME OutOfGas) /\ D <= frame_gas_left s'
Proof
  gen_tac >> Induct >> gen_tac
  >- simp[asm_run_bounded_def] >>
  first_x_assum (qspec_then `D` (qx_choose_then `b` assume_tac)) >>
  qexists_tac `64 * b + frame_op_gas H + 64 * D` >>
  rpt gen_tac >> strip_tac >>
  drule asm_run_bounded_step >> strip_tac >>
  `frame_op_gas H + 64 * D <= frame_gas_left e` by decide_tac >>
  Cases_on `s = e`
  >- (gvs[] >>
      `frame_op_gas H + 64 * D <= frame_gas_left e` by decide_tac >>
      drule_all asm_frame_current_gas >> simp[]) >>
  drule_all (cj 2 asm_frame_step) >> strip_tac
  >- (fs[frame_inst_at_step] >> metis_tac[frame_reaches_last]) >>
  drule_all frame_next_inst_at >> simp[] >> strip_tac >>
  `frame_op_gas H <= frame_gas_left e` by decide_tac >>
  drule_all asm_frame_gas_step >> strip_tac >>
  qpat_x_assum `!es1. frame_next e es1 ==> _` drule >> strip_tac >>
  `b <= (frame_gas_left e - frame_op_gas H) DIV 64` by
    (simp[X_LE_DIV] >> decide_tac) >>
  `b <= frame_gas_left es1` by
    (Cases_on `MEM (EL a.as_pc prog) [AsmOp "CALL"; AsmOp "STATICCALL";
                 AsmOp "DELEGATECALL"; AsmOp "CREATE"; AsmOp "CREATE2"]` >>
     fs[] >> decide_tac) >>
  `wf_state es1` by fs[asm_frame_rel_def] >>
  metis_tac[]
QED

Theorem asm_frame_current_no_returndatacopy[local]:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
  a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
  ~MEM (AsmOp "RETURNDATACOPY") prog ==>
  ~frame_inst_at es es ReturnDataCopy
Proof
  strip_tac >>
  `?c rb rest. es.contexts = (c,rb)::rest /\
    asm_evm_rel (prog ++ [AsmDataItem data]) a es` by
    metis_tac[asm_frame_rel_def] >>
  drule_all frame_next_opcode >> strip_tac >>
  simp[frame_inst_at_step] >> rpt strip_tac >>
  gvs[] >>
  metis_tac[frame_encode_returndatacopy, MEM_EL]
QED

(* Lockstep corollary: a frame related to a bounded run of assembly with no
   RETURNDATACOPY never reaches a ReturnDataCopy opcode at its own depth.
   Generic in prog; codegen_no_returndatacopy is its codegen instance. *)
Theorem asm_frame_no_returndatacopy:
  !N prog data es0 a e H t.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a e /\
    asm_run_bounded (SND (compute_label_offsets prog))
      (build_offset_to_pc prog) prog H N a /\
    ~MEM (AsmOp "RETURNDATACOPY") prog
    ==>
    ~frame_inst_at e t ReturnDataCopy
Proof
  Induct_on `N` >- simp[asm_run_bounded_def] >>
  rpt gen_tac >> strip_tac >>
  drule asm_run_bounded_step >> strip_tac >>
  drule_all asm_frame_current_no_returndatacopy >> strip_tac >>
  drule_all (cj 2 asm_frame_step) >> strip_tac
  >- (strip_tac >>
      `t = e` by
        (irule frame_reaches_last >> gvs[frame_inst_at_step]) >> gvs[]) >>
  gvs[] >> strip_tac >>
  `t = e \/ RTC (\a b. LENGTH a.contexts >= LENGTH e.contexts /\
      step a = (INL (),b)) es1 t` by
    (irule frame_reaches_next >> gvs[frame_inst_at_step])
  >- gvs[] >>
  first_x_assum (qspecl_then [`prog`, `data`, `es0`, `as1`, `es1`, `H`, `t`]
    mp_tac) >>
  simp[] >> gvs[frame_inst_at_step, frame_next_def] >> metis_tac[]
QED
