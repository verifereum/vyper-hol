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

(* Each of these has no memory range and is neither a terminator nor an
   INVOKE. *)
Definition fmp_inserted_op_def:
  fmp_inserted_op op <=>
    MEM op [ASSIGN; ADD; NOT; AND; BUMP; INITIAL_FMP; FMP_PARAM; RETPC_PARAM]
End

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
         (fmp_stage_root infos ctx fn) lbl bb.bb_instructions p + (j - p))
Proof
  cheat
QED

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
  cheat
QED
