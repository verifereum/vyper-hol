(*
 * The asm-to-EVM half of S7g's surplus bound, for any assembly program:
 * a frame related to an assembly state whose run is bounded (N steps,
 * memory below H) keeps D gas after each step before a RETURNDATACOPY,
 * given g gas, where g depends only on H, N and D.
 *
 * TOP-LEVEL:
 *   asm_frame_gas_surplus - the bound, generic in the program
 *)

Theory asmFrameSurplus
Ancestors
  asmFrameNext asmFrameGas asmFrameLocalStep asmFrameCallStep frameStep
  asmRunBounded asmFrameRel frameGas asmSem asmWf asmEncodeParse codegenRel
  symbolResolve vfmExecution vfmExecutionProp vfmOperation vfmContext
  callTrace list finite_map relation arithmetic

Theorem asm_frame_before_copy[local]:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a e /\
  a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
  frame_inst_at e s op /\
  (!t. frame_inst_at e t ReturnDataCopy ==>
       ~RTC (\x y. LENGTH x.contexts >= LENGTH s.contexts /\
                   step x = (INL (),y)) t s) ==>
  EL a.as_pc prog <> AsmOp "RETURNDATACOPY"
Proof
  strip_tac >> strip_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a e` by fs[asm_frame_rel_def] >>
  drule_all asm_frame_decode_setup >> strip_tac >>
  `next_opcode (FST (HD e.contexts)) = SOME ReturnDataCopy` by
    (irule asm_frame_opcode_decode >> simp[wf_opname_def] >>
     qexistsl_tac [`a`, `data`, `prog`] >>
     simp[encode_inst_def, evm_opcode_byte_def, evm_opcode_table_def,
          opcode_def]) >>
  `frame_inst_at e e ReturnDataCopy` by (irule frame_inst_at_self >> simp[]) >>
  fs[frame_inst_at_def] >> gvs[]
QED

Theorem asm_frame_current_gas[local]:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a e /\
  a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
  EL a.as_pc prog <> AsmOp "RETURNDATACOPY" /\
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
   asm_frame_step_next steps the assembly and the frame together
   (frame_reaches_next / frame_reaches_last place every frame state of
   frame_inst_at on that chain), asm_run_bounded supplies each step's
   side conditions until a RETURNDATACOPY or a terminal step, and
   asm_frame_gas_step bounds each step's cost by frame_op_gas H, with a
   call or create leaving at least (gas - frame_op_gas H) DIV 64.  So
   g = G N with G 0 = frame_op_gas H + 64 * D and
   G (SUC k) = 64 * G k + frame_op_gas H + 64 * D (or any larger
   recurrence); the 64 * D covers a CREATE whose own step keeps a 64th
   works.  A RETURNDATACOPY state before s is excluded by the hypothesis. *)
Theorem asm_frame_gas_surplus:
  !H N D. ?g. !prog data es0 a e s op r s'.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a e /\
    wf_state e /\ g <= frame_gas_left e /\
    asm_run_bounded (SND (compute_label_offsets prog))
      (build_offset_to_pc prog) prog H N a /\
    frame_inst_at e s op /\
    (!t. frame_inst_at e t ReturnDataCopy ==>
         ~RTC (\x y. LENGTH x.contexts >= LENGTH s.contexts /\
                     step x = (INL (), y)) t s) /\
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
  `EL a.as_pc prog <> AsmOp "RETURNDATACOPY"` by
    (irule asm_frame_before_copy >> metis_tac[]) >>
  fs[] >>
  `frame_op_gas H + 64 * D <= frame_gas_left e` by decide_tac >>
  Cases_on `s = e`
  >- (gvs[] >>
      `frame_op_gas H + 64 * D <= frame_gas_left e` by decide_tac >>
      drule_all asm_frame_current_gas >> simp[]) >>
  drule_all asm_frame_step_next >> strip_tac
  >- (fs[frame_inst_at_def] >> metis_tac[frame_reaches_last]) >>
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
  `!t. frame_inst_at es1 t ReturnDataCopy ==>
       ~RTC (\x y. LENGTH x.contexts >= LENGTH s.contexts /\
                   step x = (INL (),y)) t s` by
    (rpt strip_tac >> drule_all frame_next_inst_at_prefix >> metis_tac[]) >>
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
  simp[frame_inst_at_def] >> rpt strip_tac >>
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
  qpat_x_assum `asm_run_bounded _ _ _ _ _ _` mp_tac >>
  simp[Once asm_run_bounded_def] >> strip_tac >>
  `EL a.as_pc prog <> AsmOp "RETURNDATACOPY"` by
    metis_tac[MEM_EL] >>
  gvs[] >>
  `!e. asm_step (SND (compute_label_offsets prog))
    (build_offset_to_pc prog) (EL a.as_pc prog) a <> AsmError e` by
    (gen_tac >> strip_tac >> gvs[]) >>
  `~is_data_inst (EL a.as_pc prog)` by
    (Cases_on `EL a.as_pc prog` >>
     gvs[is_data_inst_def, asm_step_def]) >>
  drule_all asm_frame_current_no_returndatacopy >> strip_tac >>
  drule_all asm_frame_step_next >> strip_tac
  >- (strip_tac >>
      `t = e` by
        (irule frame_reaches_last >> gvs[frame_inst_at_def]) >> gvs[]) >>
  gvs[] >> strip_tac >>
  `t = e \/ RTC (\a b. LENGTH a.contexts >= LENGTH e.contexts /\
      step a = (INL (),b)) es1 t` by
    (irule frame_reaches_next >> gvs[frame_inst_at_def])
  >- gvs[] >>
  first_x_assum (qspecl_then [`prog`, `data`, `es0`, `as1`, `es1`, `H`, `t`]
    mp_tac) >>
  simp[] >> gvs[frame_inst_at_def, frame_next_def] >> metis_tac[]
QED
