(*
 * The memory side of FmpLowering's coverage (fmpStageCoverage): what the
 * lowered code accesses at a point related to the source.  A kept
 * instruction accesses the source's static ranges unchanged or a DALLOCA
 * site relocated to at or above the real initial fmp; a revert
 * forwarding stays one in the lowered block; the instructions the
 * lowering inserts access no memory.
 *
 * TOP-LEVEL:
 *   fmp_inserted_op         - the opcodes the lowering inserts
 *   fmp_stage_kept_mem      - a kept instruction's accesses
 *   fmp_stage_forward_lift  - revert forwarding survives the lowering
 *   fmp_stage_inserted_at   - the lowered code of a point, apart from its
 *                             kept instruction, is inserted opcodes
 *)
Theory fmpStageCoverMem
Ancestors
  fmpStageOpBase fmpStageControl fmpStageRel o1PassContract ptrDiscipline
  contextCodegenRel unitMemInv venomExecSemantics venomState venomInst
  finite_map words list
  fmpStageCoverForwardAssemble fmpStageCoverForwardBoundary
  fmpStageCoverMemAssemble fmpStageCoverMemRoot

(* Each of these has no memory range and is neither a terminator nor an
   INVOKE. *)
Definition fmp_inserted_op_def:
  fmp_inserted_op op <=>
    MEM op [ASSIGN; ADD; NOT; AND; BUMP; INITIAL_FMP; FMP_PARAM; RETPC_PARAM]
End

(* Why it holds: a nonempty range above eom, or through a pointer, lies
   in its site G v = (b,sz) (access_ok); fmp_stage_operand relates the
   pointer to its relocated site c >= fmp0 (fmp_sites_ok), with no wrap
   since c + sz <= lo <= raw (fmp_frontier_rel).  Other ranges come from
   untainted non-pointer operands (taint_ok), equal on both sides. *)
Theorem fmp_stage_kept_mem:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  EVERY (\(off,len). len = 0 \/ off + len <= eom \/ fmp0 <= off)
    (inst_mem_ranges inst t)
Proof
  cheat
QED

(* Why it holds: restores sit only at reclaim points (DALLOCA, jumps,
   needs-FMP INVOKEs), none of which lies between p and j, and the root
   never sits at a RETURNDATACOPY; so the ASSIGNs map one-to-one and
   the target pair is tidx p, tidx j = tidx p + (j - p).
   same_after_assigns is unchanged since the inserted instructions write
   only the runner, fresh temps (the real fn' pins their names) and the
   DALLOCA's own output. *)
Theorem fmp_stage_forward_lift:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ revert_forward_pair bb p j ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    revert_forward_pair bb'
      (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
         (fmp_stage_root infos ctx fn) lbl bb.bb_instructions p)
      (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
         (fmp_stage_root infos ctx fn) lbl bb.bb_instructions j)
Proof
  mp_tac fmp_cover_forward_from_prefix >>
  (impl_tac >- metis_tac[fmp_stage_copy_prefix_same_after]) >>
  metis_tac[]
QED

(* Why it holds: target indices tidx idx .. tidx (SUC idx) - 1 hold
   the plan point's restore (ASSIGN), then the image of EL idx: one kept
   inst, or ADD/NOT/AND/BUMP for DALLOCA; the root (INITIAL_FMP, or
   FMP_PARAM then RETPC_PARAM after the user params) adds one more. *)
Theorem fmp_stage_inserted_at:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (if idx = 0 then 0
   else fmp_stage_tidx (fmp_stage_plan infos ctx fn)
          (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx) <= i /\
  i < fmp_stage_tidx (fmp_stage_plan infos ctx fn)
        (fmp_stage_root infos ctx fn) lbl bb.bb_instructions (SUC idx) /\
  (i = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
         (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
       (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0) ==>
   MEM (EL idx bb.bb_instructions).inst_opcode [DALLOCA; RETPC_PARAM]) ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    i < LENGTH bb'.bb_instructions /\
    fmp_inserted_op (EL i bb'.bb_instructions).inst_opcode
Proof
  strip_tac >> irule fmp_cover_inserted_from_root >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    irule fmp_cover_root_middle >> metis_tac[]) >>
  simp[fmp_inserted_op_def] >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  gvs[] >> metis_tac[]
QED
