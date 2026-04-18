(*
 * EVM Step Simulation Infrastructure
 *
 * Core lemmas for asm_bytecode_sim:
 *   1. run_unfold: OWHILE unfolding for EVM run
 *   2. step_single_context_cases: what step returns in single-context mode
 *   3. Per-opcode correspondence helpers
 *
 * Uses gas-disjunctive approach: either EVM fails with non-StackOverflow
 * exception, or the asm and EVM steps correspond.
 *)


Theory evmStepSim
Ancestors
  asmSem codegenRel asmWf symbolResolve vfmExecution vfmContext
  vfmOperation vfmExecutionProp asmToBytecodeProofs asmParseProofs
  asmEncodeParse vfmState list rich_list pair option
  finite_map arithmetic While
Libs
  fcpLib numLib

(* ===== Dimension lemma for bytes32 = word256 ===== *)

val dim256 = fcpLib.INDEX_CONV ``dimindex(:256)``;

(* word_of_bytes_pad_encode_roundtrip specialized for bytes32 *)
val pad_encode_bytes32 =
  let val inst = INST_TYPE [alpha |-> ``:256``]
        word_of_bytes_pad_encode_roundtrip
      val r1 = REWRITE_RULE [dim256] inst
      val div_thm = EVAL ``divides 8 256``
      val leq_thm = numLib.REDUCE_CONV ``(8:num) <= 256``
  in REWRITE_RULE [div_thm, leq_thm] r1 end;

(* ===== run unfolding ===== *)

(* run es unfolds by one step *)
Theorem run_unfold:
  !es. run es =
    let (r, es1) = step es in
      case r of
        INL _ => run es1
      | INR v => SOME (INR v, es1)
Proof
  rw[run_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [OWHILE_THM])) >>
  simp[] >>
  Cases_on `step es` >> Cases_on `q` >> simp[run_def] >>
  ONCE_REWRITE_TAC [OWHILE_THM] >> simp[]
QED

(* run with one INL step *)
Theorem run_step_inl:
  !es es1.
    step es = (INL (), es1) ==>
    run es = run es1
Proof
  rw[] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [run_unfold])) >>
  simp[UNCURRY]
QED

(* run with one INR step *)
Theorem run_step_inr:
  !es r es1.
    step es = (INR r, es1) ==>
    run es = SOME (INR r, es1)
Proof
  rw[] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [run_unfold])) >>
  simp[UNCURRY]
QED

(* ===== EVM monad helpers ===== *)

(* bind returns INR if first computation returns INR *)
Theorem bind_inr:
  !f g es r es'.
    f es = (INR r, es') ==>
    bind f g es = (INR r, es')
Proof
  rw[bind_def]
QED

(* bind returns INL if both computations return INL *)
Theorem bind_inl:
  !f g es x es1 y es2.
    f es = (INL x, es1) /\
    g x es1 = (INL y, es2) ==>
    bind f g es = (INL y, es2)
Proof
  rw[bind_def]
QED

(* ignore_bind = bind ignoring the value *)
Theorem ignore_bind_inr:
  !f g es r es'.
    f es = (INR r, es') ==>
    ignore_bind f g es = (INR r, es')
Proof
  rw[ignore_bind_def, bind_def]
QED

Theorem ignore_bind_inl:
  !f g es u es1.
    f es = (INL u, es1) ==>
    ignore_bind f g es = g es1
Proof
  rw[ignore_bind_def, bind_def] >> Cases_on `u` >> simp[]
QED

(* get_current_context with non-empty contexts *)
Theorem get_current_context_cons:
  !ctxt rb rest es.
    es.contexts = (ctxt, rb) :: rest ==>
    get_current_context es = (INL ctxt, es)
Proof
  rw[get_current_context_def, return_def]
QED

(* set_current_context with non-empty contexts *)
Theorem set_current_context_cons:
  !ctxt' es ctxt rb rest.
    es.contexts = (ctxt, rb) :: rest ==>
    set_current_context ctxt' es =
      (INL (), es with contexts := (ctxt', rb) :: rest)
Proof
  rw[set_current_context_def, return_def]
QED

(* consume_gas either succeeds or fails with OutOfGas *)
Theorem consume_gas_cases:
  !n es ctxt rb rest.
    es.contexts = (ctxt, rb) :: rest ==>
    (ctxt.gasUsed + n <= ctxt.msgParams.gasLimit /\
     consume_gas n es =
       (INL (), es with contexts :=
         (ctxt with gasUsed := ctxt.gasUsed + n, rb) :: rest)) \/
    (~(ctxt.gasUsed + n <= ctxt.msgParams.gasLimit) /\
     consume_gas n es = (INR (SOME OutOfGas), es))
Proof
  rw[consume_gas_def, bind_def, ignore_bind_def,
     get_current_context_def, return_def,
     set_current_context_def, assert_def] >>
  Cases_on `ctxt.gasUsed + n <= ctxt.msgParams.gasLimit` >>
  simp[execution_state_component_equality]
QED

(* push_stack either succeeds or fails with StackOverflow *)
Theorem push_stack_cases:
  !v es ctxt rb rest.
    es.contexts = (ctxt, rb) :: rest ==>
    (LENGTH ctxt.stack < stack_limit /\
     push_stack v es =
       (INL (), es with contexts :=
         (ctxt with stack := v :: ctxt.stack, rb) :: rest)) \/
    (~(LENGTH ctxt.stack < stack_limit) /\
     push_stack v es = (INR (SOME StackOverflow), es))
Proof
  rw[push_stack_def, bind_def, ignore_bind_def,
     get_current_context_def, return_def,
     set_current_context_def, assert_def] >>
  Cases_on `LENGTH ctxt.stack < stack_limit` >>
  simp[execution_state_component_equality]
QED

(* pop_stack with enough elements *)
Theorem pop_stack_ok:
  !n es ctxt rb rest.
    es.contexts = (ctxt, rb) :: rest /\
    n <= LENGTH ctxt.stack ==>
    pop_stack n es =
      (INL (TAKE n ctxt.stack),
       es with contexts :=
         (ctxt with stack := DROP n ctxt.stack, rb) :: rest)
Proof
  rw[pop_stack_def, bind_def, ignore_bind_def,
     get_current_context_def, return_def,
     set_current_context_def, assert_def]
QED

(* pop_stack with too few elements *)
Theorem pop_stack_underflow:
  !n es ctxt rb rest.
    es.contexts = (ctxt, rb) :: rest /\
    ~(n <= LENGTH ctxt.stack) ==>
    pop_stack n es = (INR (SOME StackUnderflow), es)
Proof
  rw[pop_stack_def, bind_def, ignore_bind_def,
     get_current_context_def, return_def,
     assert_def]
QED

(* ===== Per-step correspondence ===== *)

(* ===== Handle step with single context ===== *)

(* When there is exactly one EVM context and the exception is not an
   abort, handle_step returns (INR (SOME exc'), ...) with exc' <> StackOverflow.
   This is because handle_exception checks get_num_contexts:
   n <= 1 => reraise e (which is (INR e, state)).
   If consume_gas gasLeft fails, it produces OutOfGas <> StackOverflow.
   
   This lemma handles the OutOfGas case for ALL instruction proofs. *)
Theorem handle_step_single_context:
  !exc es.
    LENGTH es.contexts = 1 /\
    ~vfm_abort (SOME exc) /\
    exc <> StackOverflow ==>
    ?es1 exc'. handle_step (SOME exc) es = (INR (SOME exc'), es1) /\
               exc' <> StackOverflow
Proof
  rpt strip_tac >>
  Cases_on `es.contexts` >> fs[] >>
  Cases_on `h` >> gvs[] >>
  simp[handle_step_def, handle_def, handle_create_def,
       bind_def, ignore_bind_def,
       get_return_data_def, get_output_to_def,
       get_current_context_def, return_def, reraise_def] >>
  Cases_on `q.msgParams.outputTo` >> simp[reraise_def] >>
  simp[handle_exception_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def] >> (
    Cases_on `exc = Reverted`
    >- (gvs[] >>
        simp[get_num_contexts_def, return_def, bind_def, reraise_def,
             exception_distinct])
    >> simp[] >>
    simp[get_gas_left_def, bind_def, get_current_context_def, return_def,
         consume_gas_def, ignore_bind_def, set_current_context_def,
         assert_def] >>
    Cases_on `q.msgParams.gasLimit - q.gasUsed + q.gasUsed <=
              q.msgParams.gasLimit`
    >- (simp[set_return_data_def, bind_def, get_current_context_def,
             return_def, set_current_context_def,
             get_num_contexts_def, reraise_def])
    >> simp[exception_distinct]
  )
QED

(* AsmLabel: JUMPDEST — consume_gas 1, increment PC *)
Theorem asm_evm_step_label:
  !prog as es lbl.
    asm_wf prog /\
    asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmLabel lbl /\
    LENGTH as.as_stack < stack_limit /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               exc <> StackOverflow) \/
    ?es1. step es = (INL (), es1) /\
          asm_evm_rel prog (asm_next as) es1 /\
          LENGTH es1.contexts = 1
Proof
  rpt strip_tac >>
  fs[asm_evm_rel_def] >>
  Cases_on `es.contexts` >> fs[] >>
  Cases_on `h` >> fs[] >>
  Cases_on `t` >> fs[] >>
  rename1 `[(ctxt, rb)]` >>
  (* Get parsed opname at current offset + wf_opname *)
  `?op. FLOOKUP (parse_code 0 FEMPTY (assemble prog))
                (asm_pc_to_offset prog as.as_pc) = SOME op /\
        opcode op = encode_inst (SND (compute_label_offsets prog))
                                (EL as.as_pc prog) /\
        wf_opname op` by
    (irule assemble_parse_exact >> simp[]) >>
  `opcode op = [91w]` by simp[encode_inst_def] >>
  `op = JumpDest` by
    (irule opcode_byte_91_is_jumpdest >> simp[]) >>
  gvs[] >>
  `asm_pc_to_offset prog as.as_pc < LENGTH (assemble prog)` by
    (irule offset_in_bounds >> simp[]) >>
  simp[step_def, handle_def] >>
  simp[bind_def, ignore_bind_def, get_current_context_def, return_def] >>
  simp[step_inst_def, static_gas_def] >>
  mp_tac (Q.SPECL [`1`, `es`, `ctxt`, `rb`, `[]`] consume_gas_cases) >>
  (impl_tac >- simp[]) >>
  strip_tac >> simp[]
  (* Case 1: gas sufficient — step succeeds *)
  >- (simp[inc_pc_or_jump_def, is_call_def, LET_THM, opcode_def,
           bind_def, get_current_context_def, return_def,
           set_current_context_def, asm_next_def] >>
      ONCE_REWRITE_TAC[GSYM ADD1] >>
      simp[asm_pc_to_offset_suc, asm_inst_size_def])
  (* Case 2: OutOfGas — handle_step returns INR *)
  >> DISJ1_TAC >>
     mp_tac (Q.SPECL [`OutOfGas`, `es`] handle_step_single_context) >>
     simp[exception_distinct]
QED

(* ===== Per-instruction type lemmas ===== *)

(* Preamble extraction: given asm_evm_rel and the standard preconditions,
   extract the EVM context, the parsed opcode, and key equalities. *)
Theorem asm_evm_step_setup:
  !prog as es.
    asm_wf prog /\
    asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\
    ~is_data_inst (EL as.as_pc prog) /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) ==>
    ?ctxt rb op.
      es.contexts = [(ctxt, rb)] /\
      FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME op /\
      wf_opname op /\
      opcode op = encode_inst (SND (compute_label_offsets prog))
                              (EL as.as_pc prog) /\
      ~(LENGTH (assemble prog) <= ctxt.pc) /\
      ctxt.msgParams.code = assemble prog /\
      ctxt.msgParams.parsed = parse_code 0 FEMPTY (assemble prog) /\
      ctxt.stack = as.as_stack /\
      ctxt.memory = as.as_memory /\
      ctxt.pc = asm_pc_to_offset prog as.as_pc /\
      ctxt.jumpDest = NONE /\
      ctxt.returnData = as.as_returndata /\
      ctxt.logs = as.as_logs /\
      es.rollback.accounts = as.as_accounts /\
      es.rollback.tStorage = as.as_transient /\
      (!a. ctxt.msgParams.outputTo <> Code a)
Proof
  rpt strip_tac >>
  fs[asm_evm_rel_def] >>
  Cases_on `es.contexts` >> fs[] >>
  Cases_on `h` >> fs[] >>
  Cases_on `t` >> fs[] >>
  rename1 `[(ctxt1, rb1)]` >>
  (* Get parsed opname at current offset + wf_opname *)
  `?op. FLOOKUP (parse_code 0 FEMPTY (assemble prog))
                (asm_pc_to_offset prog as.as_pc) = SOME op /\
        opcode op = encode_inst (SND (compute_label_offsets prog))
                                (EL as.as_pc prog) /\
        wf_opname op` by
    (irule assemble_parse_exact >> simp[]) >>
  `asm_pc_to_offset prog as.as_pc < LENGTH (assemble prog)` by
    (irule offset_in_bounds >> simp[]) >>
  qexists_tac `op` >> simp[]
QED

(* ===== PC step correspondence ===== *)

(* ===== Shared push-value helper ===== *)

(* When the EVM parsed opname is a non-call opname with step_inst that
   does consume_gas + push_stack, and the pushed value matches the asm
   pushed value, asm_evm_rel is preserved. *)
Theorem evm_push_step[local]:
  !prog as es op v gas_cost.
    asm_wf prog /\
    asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\
    ~is_data_inst (EL as.as_pc prog) /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit /\
    opcode op = encode_inst (SND (compute_label_offsets prog))
                            (EL as.as_pc prog) /\
    wf_opname op /\
    ~is_call op /\
    step_inst op = (do consume_gas gas_cost; push_stack v od) ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               exc <> StackOverflow) \/
    ?es1. step es = (INL (), es1) /\
          asm_evm_rel prog
            (asm_next (as with as_stack := v :: as.as_stack)) es1 /\
          LENGTH es1.contexts = 1
Proof
  rpt strip_tac >>
  drule_all asm_evm_step_setup >> strip_tac >>
  `op' = op` by metis_tac[opcode_wf_inj] >> gvs[] >>
  simp[step_def, handle_def] >>
  simp[bind_def, ignore_bind_def, get_current_context_def, return_def] >>
  ASM_REWRITE_TAC[] >>
  simp[] >>
  mp_tac (Q.SPECL [`gas_cost`, `es`, `ctxt`, `rb`, `[]`]
    consume_gas_cases) >>
  (impl_tac >- simp[]) >> strip_tac >> simp[]
  >- (
    (* Gas sufficient — inline push_stack + inc_pc_or_jump *)
    simp[push_stack_def, bind_def, ignore_bind_def, LET_THM,
         get_current_context_def, return_def,
         set_current_context_def, assert_def] >>
    fs[] >>
    simp[inc_pc_or_jump_def, LET_THM,
         bind_def, get_current_context_def, return_def,
         set_current_context_def, is_call_def] >>
    qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
    simp[asm_evm_rel_def] >> strip_tac >>
    simp[asm_evm_rel_def, asm_next_def] >>
    ONCE_REWRITE_TAC[GSYM ADD1] >>
    simp[asm_pc_to_offset_suc] >>
    irule ewi_length >>
    fs[asm_wf_def, asm_encoding_wf_def, LET_THM,
       encoding_wf_inst_def, pairTheory.UNCURRY] >>
    metis_tac[]
  )
  >- (
    (* OutOfGas *)
    DISJ1_TAC >>
    mp_tac (Q.SPECL [`OutOfGas`, `es`] handle_step_single_context) >>
    simp[exception_distinct]
  )
QED

(* ===== Inline tactics for asm_evm_step opcode cases ===== *)

(* ===== Pre-proved byte-to-opname theorems ===== *)
(* Each proves: wf_opname op /\ opcode op = [byte] ==> op = ConcreteOp
   Proved once at file-load time via Cases_on op (84 constructors). *)
local
  val byte_opname_proof = fn (byte_tm, opn_tm) =>
    prove(mk_imp(mk_conj(``wf_opname (op:opname)``,
            mk_eq(``opcode (op:opname)``,
                  listSyntax.mk_list([byte_tm], ``:word8``))),
          mk_eq(``op:opname``, opn_tm)),
      Cases_on `op` >> simp[opcode_def, wf_opname_def] >>
      rpt strip_tac >>
      gvs[wordsTheory.n2w_11, wordsTheory.dimword_8,
          wordsTheory.word_add_n2w])
in
  val byte_opname_thms = map byte_opname_proof [
    (* Arith *)
    (``1w:word8``, ``Add:opname``), (``2w:word8``, ``Mul:opname``),
    (``3w:word8``, ``Sub:opname``), (``4w:word8``, ``Div:opname``),
    (``5w:word8``, ``SDiv:opname``), (``6w:word8``, ``Mod:opname``),
    (``7w:word8``, ``SMod:opname``), (``8w:word8``, ``AddMod:opname``),
    (``9w:word8``, ``MulMod:opname``), (``10w:word8``, ``Exp:opname``),
    (``11w:word8``, ``SignExtend:opname``),
    (* Compare *)
    (``16w:word8``, ``LT:opname``), (``17w:word8``, ``GT:opname``),
    (``18w:word8``, ``SLT:opname``), (``19w:word8``, ``SGT:opname``),
    (``20w:word8``, ``Eq:opname``), (``21w:word8``, ``IsZero:opname``),
    (* Bitwise *)
    (``22w:word8``, ``And:opname``), (``23w:word8``, ``Or:opname``),
    (``24w:word8``, ``XOr:opname``), (``25w:word8``, ``Not:opname``),
    (``26w:word8``, ``Byte:opname``), (``27w:word8``, ``ShL:opname``),
    (``28w:word8``, ``ShR:opname``), (``29w:word8``, ``SAR:opname``),
    (* Dup 0..15 *)
    (``128w:word8``, ``Dup 0``), (``129w:word8``, ``Dup 1``),
    (``130w:word8``, ``Dup 2``), (``131w:word8``, ``Dup 3``),
    (``132w:word8``, ``Dup 4``), (``133w:word8``, ``Dup 5``),
    (``134w:word8``, ``Dup 6``), (``135w:word8``, ``Dup 7``),
    (``136w:word8``, ``Dup 8``), (``137w:word8``, ``Dup 9``),
    (``138w:word8``, ``Dup 10``), (``139w:word8``, ``Dup 11``),
    (``140w:word8``, ``Dup 12``), (``141w:word8``, ``Dup 13``),
    (``142w:word8``, ``Dup 14``), (``143w:word8``, ``Dup 15``),
    (* Swap 0..15 *)
    (``144w:word8``, ``Swap 0``), (``145w:word8``, ``Swap 1``),
    (``146w:word8``, ``Swap 2``), (``147w:word8``, ``Swap 3``),
    (``148w:word8``, ``Swap 4``), (``149w:word8``, ``Swap 5``),
    (``150w:word8``, ``Swap 6``), (``151w:word8``, ``Swap 7``),
    (``152w:word8``, ``Swap 8``), (``153w:word8``, ``Swap 9``),
    (``154w:word8``, ``Swap 10``), (``155w:word8``, ``Swap 11``),
    (``156w:word8``, ``Swap 12``), (``157w:word8``, ``Swap 13``),
    (``158w:word8``, ``Swap 14``), (``159w:word8``, ``Swap 15``),
    (* Context ops *)
    (``48w:word8``, ``Address:opname``), (``49w:word8``, ``Balance:opname``),
    (``50w:word8``, ``Origin:opname``), (``51w:word8``, ``Caller:opname``),
    (``52w:word8``, ``CallValue:opname``), (``53w:word8``, ``CallDataLoad:opname``),
    (``54w:word8``, ``CallDataSize:opname``), (``56w:word8``, ``CodeSize:opname``),
    (``58w:word8``, ``GasPrice:opname``), (``59w:word8``, ``ExtCodeSize:opname``),
    (``61w:word8``, ``ReturnDataSize:opname``), (``63w:word8``, ``ExtCodeHash:opname``),
    (``64w:word8``, ``BlockHash:opname``), (``65w:word8``, ``CoinBase:opname``),
    (``66w:word8``, ``TimeStamp:opname``), (``67w:word8``, ``Number:opname``),
    (``68w:word8``, ``PrevRandao:opname``), (``69w:word8``, ``GasLimit:opname``),
    (``70w:word8``, ``ChainId:opname``), (``71w:word8``, ``SelfBalance:opname``),
    (``72w:word8``, ``BaseFee:opname``), (``73w:word8``, ``BlobHash:opname``),
    (``74w:word8``, ``BlobBaseFee:opname``), (``90w:word8``, ``Gas:opname``),
    (* Memory/Storage *)
    (``81w:word8``, ``MLoad:opname``), (``82w:word8``, ``MStore:opname``),
    (``83w:word8``, ``MStore8:opname``), (``84w:word8``, ``SLoad:opname``),
    (``85w:word8``, ``SStore:opname``), (``89w:word8``, ``MSize:opname``),
    (``92w:word8``, ``TLoad:opname``), (``93w:word8``, ``TStore:opname``),
    (``32w:word8``, ``Keccak256:opname``), (``94w:word8``, ``MCopy:opname``),
    (* Control *)
    (``0w:word8``, ``Stop:opname``), (``80w:word8``, ``Pop:opname``),
    (``86w:word8``, ``Jump:opname``), (``87w:word8``, ``JumpI:opname``),
    (``91w:word8``, ``JumpDest:opname``),
    (``243w:word8``, ``Return:opname``), (``253w:word8``, ``Revert:opname``),
    (``254w:word8``, ``Invalid:opname``), (``255w:word8``, ``SelfDestruct:opname``),
    (* Copy *)
    (``55w:word8``, ``CallDataCopy:opname``), (``57w:word8``, ``CodeCopy:opname``),
    (``60w:word8``, ``ExtCodeCopy:opname``), (``62w:word8``, ``ReturnDataCopy:opname``),
    (* Log *)
    (``160w:word8``, ``Log 0``), (``161w:word8``, ``Log 1``),
    (``162w:word8``, ``Log 2``), (``163w:word8``, ``Log 3``),
    (``164w:word8``, ``Log 4``)
  ]
end;

(* handle_step NONE with single non-Code context: (INR NONE, es) *)
Theorem handle_step_none_single_context:
  !es ctxt rb.
    es.contexts = [(ctxt, rb)] /\
    (!a. ctxt.msgParams.outputTo <> Code a) ==>
    handle_step NONE es = (INR NONE, es)
Proof
  rpt strip_tac >>
  simp[handle_step_def, vfm_abort_def, handle_def] >>
  simp[handle_create_def, bind_def, ignore_bind_def,
       get_return_data_def, get_output_to_def,
       get_current_context_def, return_def, reraise_def] >>
  Cases_on `ctxt.msgParams.outputTo` >> gvs[] >>
  simp[handle_exception_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def,
       get_num_contexts_def, reraise_def]
QED

(* handle_step (SOME Reverted) with single context: state preserved *)
Theorem handle_step_reverted_single_context:
  !es ctxt rb.
    es.contexts = [(ctxt, rb)] ==>
    handle_step (SOME Reverted) es = (INR (SOME Reverted), es)
Proof
  rpt strip_tac >>
  Cases_on `ctxt.msgParams.outputTo` >> gvs[] >>
  simp[handle_step_def, vfm_abort_def, handle_def,
       handle_create_def, handle_exception_def,
       bind_def, ignore_bind_def,
       get_return_data_def, get_output_to_def,
       get_current_context_def, return_def, reraise_def,
       get_num_contexts_def,
       exception_distinct, exception_11, LET_THM]
QED

(* Close gas-OK, gas-fail, or abort-error after IF_CASES_TAC >> simp[]
   Tries gas-fail first (fast match_mp_tac check),
   then abort errors, then gas-OK. *)

(* update_storage k v = (k =+ v): eta-reduced for record normalisation *)
val update_storage_eta =
  prove(``update_storage k v = (k =+ v)``,
  simp[FUN_EQ_THM, update_storage_def]);

val gas_close_tac : tactic =
  FIRST [
    (* Non-abort errors: try common exceptions *)
    DISJ1_TAC >>
    FIRST (map (fn exc =>
      match_mp_tac (Q.SPEC exc handle_step_single_context |>
        SIMP_RULE (srw_ss()) [vfm_abort_def, exception_distinct]) >>
      simp[])
    [`OutOfGas`, `WriteInStaticContext`, `StackUnderflow`]),
    (* Abort errors (OutsideDomain etc.): handle_step returns (INR, es) directly *)
    DISJ1_TAC >>
    (fn (asl, g) =>
      if can (find_term (can (match_term ``handle_step (SOME exc) es``))) g
      then ALL_TAC (asl, g)
      else raise (mk_HOL_ERR "" "" "no handle_step")) >>
    simp[handle_step_def, reraise_def, vfm_abort_def] >>
    simp[exception_distinct, exception_11],
    (* Gas OK: full correspondence *)
    DISJ2_TAC >>
    simp[inc_pc_or_jump_def, LET_THM, opcode_def,
         bind_def, get_current_context_def, return_def,
         set_current_context_def, is_call_def] >>
    qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
    simp[asm_evm_rel_def, update_storage_eta] >> strip_tac >>
    gvs[asm_evm_rel_def, asm_next_def, LET_THM, update_storage_eta,
        account_state_component_equality] >>
    ONCE_REWRITE_TAC[GSYM arithmeticTheory.ADD1] >>
    simp[asm_pc_to_offset_suc, asm_inst_size_def]
  ];

(* Fast opname identification:
   1. EVAL the encode_inst RHS to get concrete byte
   2. Use pre-proved byte-to-opname theorem *)
val identify_evm_op_tac : tactic =
  qpat_x_assum `opcode _ = encode_inst _ _` (fn th =>
    assume_tac (CONV_RULE (RAND_CONV EVAL) th)) >>
  FIRST (map (fn th =>
    SUBGOAL_THEN (snd(dest_imp(concl th))) SUBST_ALL_TAC >-
    (mp_tac th >> ASM_REWRITE_TAC[]))
  byte_opname_thms);

(*  Call-like asm names that create new EVM contexts.
    asm_evm_step handles single-context execution only;
    these names need multi-step correspondence proved separately. *)
Definition is_evm_call_name_def:
  is_evm_call_name name <=>
    name = "CALL" \/ name = "STATICCALL" \/
    name = "DELEGATECALL" \/ name = "CREATE" \/ name = "CREATE2" \/
    name = "SELFDESTRUCT"
End

Definition no_asm_calls_def:
  no_asm_calls prog <=>
    !i name. i < LENGTH prog /\ EL i prog = AsmOp name ==>
             ~is_evm_call_name name
End

(* Setup + category expansion tactic *)
val category_setup_tac : tactic =
  rpt strip_tac >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  drule_all asm_evm_step_setup >> strip_tac;

Theorem asm_evm_step_compare_dispatch[local]:
  !prog as es name r.
    asm_wf prog /\ asm_evm_rel prog as es /\ LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit /\
    asm_step_compare name as = SOME r ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> StackOverflow) \/
    (case r of
       AsmOK as1 => ?es1. step es = (INL (), es1) /\
                           asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
     | AsmHalt as1 => ?es1. step es = (INR NONE, es1) /\ asm_evm_rel prog as1 es1
     | AsmRevert as1 => ?es1. step es = (INR (SOME Reverted), es1) /\
                               asm_evm_rel prog as1 es1
     | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\
                                  exc <> Reverted /\ asm_evm_rel prog as1 es1
     | AsmError _ => T)
Proof
  category_setup_tac >>
  qpat_x_assum `asm_step_compare _ _ = _` mp_tac >>
  simp[asm_step_compare_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[] >>
  identify_evm_op_tac >> gvs[] >>
  simp[asm_binop_def, asm_unop_def, asm_next_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, step_binop_def, step_monop_def,
       pop_stack_def, consume_gas_def, push_stack_def,
       assert_def, LET_THM] >>
  fs[] >> IF_CASES_TAC >> simp[] >>
  gas_close_tac
QED

Theorem asm_evm_step_bitwise_dispatch[local]:
  !prog as es name r.
    asm_wf prog /\ asm_evm_rel prog as es /\ LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit /\
    asm_step_bitwise name as = SOME r ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> StackOverflow) \/
    (case r of
       AsmOK as1 => ?es1. step es = (INL (), es1) /\
                           asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
     | AsmHalt as1 => ?es1. step es = (INR NONE, es1) /\ asm_evm_rel prog as1 es1
     | AsmRevert as1 => ?es1. step es = (INR (SOME Reverted), es1) /\
                               asm_evm_rel prog as1 es1
     | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\
                                  exc <> Reverted /\ asm_evm_rel prog as1 es1
     | AsmError _ => T)
Proof
  category_setup_tac >>
  qpat_x_assum `asm_step_bitwise _ _ = _` mp_tac >>
  simp[asm_step_bitwise_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[] >>
  identify_evm_op_tac >> gvs[] >>
  simp[asm_binop_def, asm_unop_def, asm_next_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, step_binop_def, step_monop_def,
       pop_stack_def, consume_gas_def, push_stack_def,
       assert_def, LET_THM] >>
  fs[] >> IF_CASES_TAC >> simp[] >>
  gas_close_tac
QED

Theorem asm_evm_step_arith_dispatch[local]:
  !prog as es name r.
    asm_wf prog /\ asm_evm_rel prog as es /\ LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit /\
    asm_step_arith name as = SOME r ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> StackOverflow) \/
    (case r of
       AsmOK as1 => ?es1. step es = (INL (), es1) /\
                           asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
     | AsmHalt as1 => ?es1. step es = (INR NONE, es1) /\ asm_evm_rel prog as1 es1
     | AsmRevert as1 => ?es1. step es = (INR (SOME Reverted), es1) /\
                               asm_evm_rel prog as1 es1
     | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\
                                  exc <> Reverted /\ asm_evm_rel prog as1 es1
     | AsmError _ => T)
Proof
  category_setup_tac >>
  qpat_x_assum `asm_step_arith _ _ = _` mp_tac >>
  simp[asm_step_arith_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[] >>
  identify_evm_op_tac >> gvs[] >>
  simp[asm_binop_def, asm_ternop_def, asm_next_def, with_zero_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, step_binop_def, step_modop_def, step_exp_def,
       pop_stack_def, consume_gas_def, push_stack_def,
       assert_def, LET_THM, with_zero_def] >>
  fs[] >> IF_CASES_TAC >> simp[] >>
  gas_close_tac
QED

(* ===== Memory expansion helpers ===== *)

(* Big-endian word_of_bytes = little-endian word_of_bytes (REVERSE bytes)
   when LENGTH bs = dimindex/8. Uses be_bytes_thm + num_of_bytes route. *)
Theorem word_of_bytes_be_le[local]:
  !bs:word8 list.
    8 <= dimindex(:'a) /\ divides 8 (dimindex(:'a)) /\
    (LENGTH bs = dimindex(:'a) DIV 8) ==>
    word_of_bytes T (0w:'a word) bs = word_of_bytes F (0w:'a word) (REVERSE bs)
Proof
  rpt strip_tac >>
  REWRITE_TAC[GSYM byteTheory.word_of_bytes_be_def,
              GSYM byteTheory.word_of_bytes_le_def] >>
  simp[cv_stdTheory.word_of_bytes_be_eq_num_of_bytes,
       cv_stdTheory.word_of_bytes_le_eq_num_of_bytes] >>
  `TAKE (dimindex(:'a) DIV 8) (bs ++ REPLICATE (dimindex(:'a) DIV 8) 0w) = bs`
  by (ONCE_REWRITE_TAC[GSYM (ASSUME ``LENGTH (bs:word8 list) = dimindex(:'a) DIV 8``)] >>
      simp[TAKE_LENGTH_APPEND]) >>
  simp[byteTheory.be_bytes_thm]
QED

(* Specialization for 256-bit words *)
val word_of_bytes_be_le_256 =
  word_of_bytes_be_le
  |> INST_TYPE [alpha |-> ``:256``]
  |> REWRITE_RULE [dim256]
  |> SIMP_RULE (srw_ss()) [EVAL ``divides 8 256``];

(* asm_expand_memory agrees with EVM expand_memory.
   After expanding, both sides produce the same memory. *)
Theorem asm_expand_eq_evm[local]:
  !n (mem:byte list).
    asm_expand_memory n mem =
    mem ++ REPLICATE (MAX (LENGTH mem) (((n + 31) DIV 32) * 32) -
                     LENGTH mem) (0w:byte)
Proof
  rpt gen_tac >>
  simp[asm_expand_memory_def, LET_THM] >>
  Cases_on `((n + 31) DIV 32) * 32 <= LENGTH mem` >> simp[MAX_DEF]
QED

(* word_to_bytes big-endian = REVERSE(little-endian) *)
Theorem word_to_bytes_be_reverse_le[local]:
  !v:'a word. word_to_bytes v T = REVERSE (word_to_bytes v F)
Proof
  simp[GSYM byteTheory.word_to_bytes_be_def,
       GSYM byteTheory.word_to_bytes_le_def,
       cv_stdTheory.word_to_bytes_be_eq_bytes_of_num,
       cv_stdTheory.word_to_bytes_le_eq_bytes_of_num]
QED

(* Simp-normalized form: simp commutes 32 * X vs X * 32, folds offset+size+31 *)
Theorem asm_expand_eq_evm_simp[local]:
  !n (mem:byte list).
    mem ++ REPLICATE (MAX (LENGTH mem) (32 * ((n + 31) DIV 32)) -
                     LENGTH mem) (0w:byte) =
    asm_expand_memory n mem
Proof
  rpt gen_tac >>
  simp[asm_expand_memory_def, LET_THM, MAX_DEF] >>
  IF_CASES_TAC >> simp[]
QED

(* n <= rounded-up n *)
Theorem n_le_round_up_32[local]:
  !n. n <= ((n + 31) DIV 32) * 32
Proof
  gen_tac >>
  `(n + 31) = (n + 31) DIV 32 * 32 + (n + 31) MOD 32 /\
   (n + 31) MOD 32 < 32` by
    (mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >> simp[]) >>
  decide_tac
QED

(* asm_expand_memory always expands to at least the requested size *)
Theorem asm_expand_memory_length[local]:
  !n (mem:byte list). n <= LENGTH (asm_expand_memory n mem)
Proof
  rpt gen_tac >> simp[asm_expand_memory_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  mp_tac (Q.SPEC `n` n_le_round_up_32) >> decide_tac
QED

(* LENGTH (TAKE sz (DROP off (asm_expand_memory n mem))) = sz
   when off + sz <= n *)
Theorem take_drop_expand_len[local]:
  !sz off n (mem : byte list).
    off + sz <= n ==>
    LENGTH (TAKE sz (DROP off (asm_expand_memory n mem))) = sz
Proof
  rpt strip_tac >>
  simp[LENGTH_TAKE_EQ] >>
  mp_tac (Q.SPECL [`n`, `mem`] asm_expand_memory_length) >>
  decide_tac
QED

(* Fold EVM expanded memory back to asm_expand_memory.
   Uses normalized form d + (z + 31) that simp produces from (d+z) + 31. *)
Theorem asm_expand_eq_evm_norm[local]:
  !d z (mem:byte list).
    mem ++ REPLICATE (MAX (LENGTH mem) (32 * ((d + (z + 31)) DIV 32)) -
                     LENGTH mem) (0w:byte) =
    asm_expand_memory (d + z) mem
Proof
  rpt gen_tac >>
  `d + (z + 31) = (d + z) + 31` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  simp[asm_expand_memory_def, LET_THM, MAX_DEF] >>
  IF_CASES_TAC >> simp[]
QED

(* MCOPY: DROP(doff + LENGTH(TAKE sz (DROP soff expanded))) = DROP(doff + sz)
   when expanded = asm_expand_memory (MAX (soff+sz) (doff+sz)) mem *)
Theorem mcopy_drop_eq[local]:
  !doff soff sz (mem:byte list).
    let expanded = asm_expand_memory (MAX (soff + sz) (doff + sz)) mem in
    DROP (doff + LENGTH (TAKE sz (DROP soff expanded))) expanded =
    DROP (doff + sz) expanded
Proof
  rpt gen_tac >> simp[LET_THM] >>
  `soff + sz <= MAX (soff + sz) (doff + sz)` by simp[] >>
  mp_tac (Q.SPECL [`MAX (soff+sz) (doff+sz)`, `mem`]
    asm_expand_memory_length) >>
  strip_tac >>
  `LENGTH (TAKE sz (DROP soff
    (asm_expand_memory (MAX (soff+sz) (doff+sz)) mem))) = sz`
    by simp[listTheory.LENGTH_TAKE_EQ] >>
  simp[]
QED

Theorem asm_evm_step_memory_dispatch[local]:
  !prog as es name r.
    asm_wf prog /\ asm_evm_rel prog as es /\ LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit /\
    asm_step_memory name as = SOME r ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> StackOverflow) \/
    (case r of
       AsmOK as1 => ?es1. step es = (INL (), es1) /\
                           asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
     | AsmHalt as1 => ?es1. step es = (INR NONE, es1) /\ asm_evm_rel prog as1 es1
     | AsmRevert as1 => ?es1. step es = (INR (SOME Reverted), es1) /\
                               asm_evm_rel prog as1 es1
     | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\
                                  exc <> Reverted /\ asm_evm_rel prog as1 es1
     | AsmError _ => T)
Proof
  category_setup_tac >>
  qpat_x_assum `asm_step_memory _ _ = _` mp_tac >>
  simp[asm_step_memory_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[]
  (* 11 cases: POP, MLOAD, MSTORE, MSTORE8, MCOPY, MEMTOP,
               SLOAD, SSTORE, TLOAD, TSTORE, SHA3 *)
  (* === POP === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_pop_def] >>
    Cases_on `as.as_stack` >> gvs[] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_pop_def, pop_stack_def,
         consume_gas_def, assert_def, LET_THM] >>
    fs[] >> IF_CASES_TAC >> simp[] >>
    gas_close_tac
  )
  (* === MLOAD === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_mload_def, LET_THM] >>
    Cases_on `as.as_stack` >> gvs[] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_mload_def, pop_stack_def,
         consume_gas_def, push_stack_def,
         memory_expansion_info_def, expand_memory_def,
         read_memory_def, vfmConstantsTheory.word_size_def,
         assert_def, fail_def, LET_THM] >>
    IF_CASES_TAC >> gvs[]
    (* Gas OK *)
    >- (
      DISJ2_TAC >>
      simp[inc_pc_or_jump_def, LET_THM, opcode_def,
           bind_def, get_current_context_def, return_def,
           set_current_context_def, is_call_def] >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >>
      gvs[asm_evm_rel_def, asm_next_def, LET_THM] >>
      ONCE_REWRITE_TAC[GSYM arithmeticTheory.ADD1] >>
      simp[asm_pc_to_offset_suc, asm_inst_size_def] >>
      (* Memory equality: EVM expanded form = asm_expand_memory *)
      conj_tac
      >- (
        `as.as_memory ++ REPLICATE
           (MAX (LENGTH as.as_memory)
                (32 * ((w2n h + 63) DIV 32)) -
            LENGTH as.as_memory) (0w:byte) =
         asm_expand_memory (w2n h + 32) as.as_memory`
        by (simp[asm_expand_memory_def, LET_THM, MAX_DEF] >>
            IF_CASES_TAC >> simp[]) >>
        simp[] >>
        `LENGTH (TAKE 32 (DROP (w2n h)
           (asm_expand_memory (w2n h + 32) as.as_memory))) = 32`
        by (simp[LENGTH_TAKE_EQ] >>
            `w2n h + 32 <= LENGTH (asm_expand_memory (w2n h + 32) as.as_memory)`
            by simp[asm_expand_memory_length] >> simp[]) >>
        imp_res_tac word_of_bytes_be_le_256 >>
        pop_assum (fn th => REWRITE_TAC[th])
      ) >>
      simp[asm_expand_memory_def, LET_THM, MAX_DEF] >>
      IF_CASES_TAC >> simp[]
    ) >>
    (* Gas fail *)
    gas_close_tac
  )
  (* === MSTORE === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_mstore_def, LET_THM] >>
    Cases_on `as.as_stack` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_mstore_def, pop_stack_def,
         consume_gas_def,
         memory_expansion_info_def, expand_memory_def,
         write_memory_def, vfmConstantsTheory.word_size_def,
         assert_def, fail_def, LET_THM] >>
    IF_CASES_TAC >> gvs[]
    (* Gas OK *)
    >- (
      DISJ2_TAC >>
      simp[inc_pc_or_jump_def, LET_THM, opcode_def,
           bind_def, get_current_context_def, return_def,
           set_current_context_def, is_call_def] >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >>
      gvs[asm_evm_rel_def, asm_next_def, LET_THM,
          word_to_bytes_be_reverse_le,
          asm_expand_memory_def, MAX_DEF] >>
      REWRITE_TAC[dim256] >>
      rpt (IF_CASES_TAC >> gvs[]) >>
      ONCE_REWRITE_TAC[GSYM arithmeticTheory.ADD1] >>
      simp[asm_pc_to_offset_suc, asm_inst_size_def]
    ) >>
    (* Gas fail *)
    gas_close_tac
  )
  (* === MSTORE8 === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_mstore8_def, LET_THM] >>
    Cases_on `as.as_stack` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_mstore_def, pop_stack_def,
         consume_gas_def,
         memory_expansion_info_def, expand_memory_def,
         write_memory_def, vfmConstantsTheory.word_size_def,
         assert_def, fail_def, LET_THM] >>
    IF_CASES_TAC >> gvs[]
    (* Gas OK *)
    >- (
      DISJ2_TAC >>
      simp[inc_pc_or_jump_def, LET_THM, opcode_def,
           bind_def, get_current_context_def, return_def,
           set_current_context_def, is_call_def] >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >>
      gvs[asm_evm_rel_def, asm_next_def, LET_THM,
          asm_expand_memory_def, MAX_DEF] >>
      rpt (IF_CASES_TAC >> gvs[]) >>
      ONCE_REWRITE_TAC[GSYM arithmeticTheory.ADD1] >>
      simp[asm_pc_to_offset_suc, asm_inst_size_def]
    ) >>
    (* Gas fail *)
    gas_close_tac
  )
  (* === MCOPY === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_mcopy_def, LET_THM] >>
    Cases_on `as.as_stack` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    Cases_on `t'` >> gvs[] >>
    (* Unfold the EVM step. Partially evaluates but leaves
       (lambda(xOffset,xSize). do...od) (if cond then p1 else p2)
       unapplied because the lambda arg is a COND (from max_expansion_range). *)
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def, step_inst_def, step_copy_to_memory_def,
         copy_to_memory_def, pop_stack_def,
         consume_gas_def, memory_expansion_info_def,
         expand_memory_def, read_memory_def, write_memory_def,
         max_expansion_range_def,
         vfmConstantsTheory.word_size_def,
         vfmConstantsTheory.memory_copy_cost_def,
         assert_def, fail_def, LET_THM] >>
    (* Split on max_expansion_range IFs to resolve COND in lambda arg.
       gvs beta-reduces the lambda. Then re-simp to unfold inner bind chain. *)
    rpt (IF_CASES_TAC >> gvs[]) >>
    simp[bind_def, ignore_bind_def, get_current_context_def, return_def,
         set_current_context_def, assert_def, fail_def, LET_THM] >>
    rpt (IF_CASES_TAC >> gvs[]) >>
    (* Gas-fail *)
    TRY (
      DISJ1_TAC >>
      FIRST (map (fn exc =>
        match_mp_tac (Q.SPEC exc handle_step_single_context |>
          SIMP_RULE (srw_ss()) [vfm_abort_def, exception_distinct]) >>
        simp[])
      [`OutOfGas`, `WriteInStaticContext`, `StackUnderflow`]) >> NO_TAC
    ) >>
    (* Gas-OK: MCOPY *)
    DISJ2_TAC >>
    simp[inc_pc_or_jump_def, LET_THM, opcode_def,
         bind_def, get_current_context_def, return_def,
         set_current_context_def, is_call_def] >>
    qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
    simp[asm_evm_rel_def] >> strip_tac >>
    gvs[asm_evm_rel_def, asm_next_def, LET_THM] >>
    ONCE_REWRITE_TAC[GSYM arithmeticTheory.ADD1] >>
    simp[asm_pc_to_offset_suc, asm_inst_size_def] >>
    (* Substitute w2n terms with fresh variables everywhere (goal +
       assumptions). SUBST_ALL_TAC updates both, unlike qabbrev_tac
       which only updates the goal. This lets OMEGA close contradictory
       branches since all arithmetic is on pure numeric variables. *)
    `?mcpy_d. mcpy_d = w2n h` by (qexists_tac `w2n h` >> simp[]) >>
    pop_assum (SUBST_ALL_TAC o SYM) >>
    `?mcpy_s. mcpy_s = w2n h'` by (qexists_tac `w2n h'` >> simp[]) >>
    pop_assum (SUBST_ALL_TAC o SYM) >>
    `?mcpy_z. mcpy_z = w2n h''` by (qexists_tac `w2n h''` >> simp[]) >>
    pop_assum (SUBST_ALL_TAC o SYM) >>
    (* Fold EVM expanded memory back to asm_expand_memory.
       PURE_REWRITE_TAC avoids simp normalizing <= to < in MAX_DEF.
       IF_CASES_TAC splits; matching branches close via
       take_drop_expand_len, contradictory ones via OMEGA. *)
    simp[asm_expand_eq_evm_norm] >>
    PURE_REWRITE_TAC[MAX_DEF] >>
    IF_CASES_TAC >> gvs[take_drop_expand_len] >>
    (* The remaining goals have mcpy_s = mcpy_d (from antisymmetric
       ¬(mcpy_s < mcpy_d) and ¬(mcpy_d < mcpy_s)) but gvs doesn't
       derive equality from paired negated strict inequalities.
       DECIDE_TAC proves the equality, then gvs substitutes. *)
    `mcpy_s = mcpy_d` by DECIDE_TAC >> gvs[take_drop_expand_len]
  )
  (* === MEMTOP === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_push_val_def, asm_next_def] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_context_def,
         consume_gas_def, push_stack_def,
         assert_def, LET_THM] >>
    fs[] >> IF_CASES_TAC >> simp[] >>
    gas_close_tac
  )
  (* === SLOAD === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_sload_def, LET_THM] >>
    Cases_on `as.as_stack` >> gvs[] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_sload_def, pop_stack_def,
         consume_gas_def, push_stack_def,
         get_callee_def, get_accounts_def,
         access_slot_def, domain_check_def,
         set_domain_def,
         lookup_storage_def, lookup_account_def,
         assert_def, fail_def, LET_THM] >>
    Cases_on `es.msdomain` >> gvs[]
    >- ((* Enforce *)
      IF_CASES_TAC >> gvs[]
      >- ((* slot in domain *)
        rpt (IF_CASES_TAC >> gvs[]) >>
        gas_close_tac) >>
      (* slot not in domain — OutsideDomain abort *)
      gas_close_tac)
    >> (* Collect *)
    rpt (IF_CASES_TAC >> gvs[]) >>
    gas_close_tac
  )
  (* === SSTORE === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_sstore_def, LET_THM] >>
    Cases_on `as.as_stack` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    (* Expand everything EXCEPT update_gas_refund *)
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_sstore_def, pop_stack_def,
         step_sstore_gas_consumption_def,
         get_gas_left_def, get_accounts_def, get_original_def,
         get_callee_def, get_static_def,
         access_slot_def, domain_check_def, set_domain_def,
         zero_warm_def,
         (* NO update_gas_refund_def here *)
         consume_gas_def,
         assert_not_static_def,
         write_storage_def, update_accounts_def,
         lookup_storage_def, lookup_account_def,
         update_storage_def, update_account_def,
         assert_def, fail_def, LET_THM] >>
    Cases_on `es.msdomain` >> gvs[] >>
    rpt (IF_CASES_TAC >> gvs[]) >>
    (* Expand update_gas_refund — pair args now resolved *)
    simp[update_gas_refund_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def, set_current_context_def] >>
    rpt (IF_CASES_TAC >> gvs[]) >>
    TRY gas_close_tac >>
    TRY (DISJ1_TAC >>
      simp[handle_step_def, reraise_def, vfm_abort_def] >>
      simp[exception_distinct, exception_11]) >>
    (* Record equalities from write_storage updated_by vs := *)
    AP_THM_TAC >> AP_TERM_TAC >>
    simp[account_state_component_equality]
  )
  (* === TLOAD === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_tload_def, LET_THM] >>
    Cases_on `as.as_stack` >> gvs[] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_sload_def, pop_stack_def,
         consume_gas_def, push_stack_def,
         get_callee_def, get_tStorage_def,
         lookup_transient_storage_def, lookup_storage_def,
         assert_def, fail_def, LET_THM] >>
    IF_CASES_TAC >> gvs[] >>
    gas_close_tac
  )
  (* === TSTORE === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_tstore_def, LET_THM] >>
    Cases_on `as.as_stack` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_sstore_def, pop_stack_def,
         consume_gas_def, push_stack_def,
         get_callee_def, get_tStorage_def, get_static_def,
         assert_not_static_def,
         write_transient_storage_def, set_tStorage_def,
         lookup_transient_storage_def, update_transient_storage_def,
         update_storage_def,
         assert_def, fail_def, LET_THM] >>
    rpt (IF_CASES_TAC >> gvs[]) >>
    gas_close_tac
  )
  (* === SHA3 === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_sha3_def, LET_THM] >>
    Cases_on `as.as_stack` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_keccak256_def, pop_stack_def,
         consume_gas_def, push_stack_def,
         memory_expansion_info_def, expand_memory_def,
         read_memory_def, vfmConstantsTheory.word_size_def,
         vfmConstantsTheory.keccak256_per_word_cost_def,
         assert_def, fail_def, LET_THM] >>
    rpt (IF_CASES_TAC >> gvs[]) >>
    TRY (
      DISJ2_TAC >>
      simp[inc_pc_or_jump_def, LET_THM, opcode_def,
           bind_def, get_current_context_def, return_def,
           set_current_context_def, is_call_def] >>
      qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
      simp[asm_evm_rel_def] >> strip_tac >>
      gvs[asm_evm_rel_def, asm_next_def, LET_THM,
          asm_expand_memory_def, MAX_DEF] >>
      rpt (IF_CASES_TAC >> gvs[]) >>
      ONCE_REWRITE_TAC[GSYM arithmeticTheory.ADD1] >>
      simp[asm_pc_to_offset_suc, asm_inst_size_def] >>
      NO_TAC
    ) >>
    (* Gas fail *)
    gas_close_tac
  )
QED

Theorem asm_evm_step_control_dispatch[local]:
  !prog as es name r.
    asm_wf prog /\ asm_evm_rel prog as es /\ LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit /\
    (!i. i < LENGTH prog ==> 0 < asm_inst_size (EL i prog)) /\
    asm_step_control (build_offset_to_pc prog) name as = SOME r ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> StackOverflow) \/
    (case r of
       AsmOK as1 => ?es1. step es = (INL (), es1) /\
                           asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
     | AsmHalt as1 => ?es1. step es = (INR NONE, es1) /\ asm_evm_rel prog as1 es1
     | AsmRevert as1 => ?es1. step es = (INR (SOME Reverted), es1) /\
                               asm_evm_rel prog as1 es1
     | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\
                                  exc <> Reverted /\ asm_evm_rel prog as1 es1
     | AsmError _ => T)
Proof
  category_setup_tac >>
  qpat_x_assum `asm_step_control _ _ _ = _` mp_tac >>
  simp[asm_step_control_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[]
  (* 7 cases: JUMP, JUMPI, JUMPDEST, STOP, RETURN, REVERT, INVALID *)
  (* === JUMP === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_jump_def] >>
    Cases_on `as.as_stack` >> simp[] >>
    rename1 `(dest:bytes32) :: stk` >>
    Cases_on `FLOOKUP (build_offset_to_pc prog) (w2n (dest:bytes32))` >> simp[] >>
    rename1 `FLOOKUP _ _ = SOME target_pc` >>
    (* EVM side: step_jump pops dest, consumes gas, sets jumpDest *)
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_jump_def, pop_stack_def,
         consume_gas_def, assert_def, LET_THM,
         set_jump_dest_def] >>
    fs[] >>
    (* Gas check: IF_CASES_TAC puts gas-OK first *)
    IF_CASES_TAC >> simp[]
    (* Gas OK *)
    >- (
      simp[inc_pc_or_jump_def, LET_THM,
           bind_def, get_current_context_def, return_def,
           set_current_context_def, is_call_def, opcode_def,
           assert_def, ignore_bind_def] >>
      (* Jump dest validation IF: valid first, invalid second *)
      IF_CASES_TAC >> simp[]
      (* Jump dest valid *)
      >- (
        (* Use offset_to_pc_reverse to get target_pc properties *)
        `target_pc < LENGTH prog ∧
         asm_pc_to_offset prog target_pc = w2n dest` by (
          irule offset_to_pc_reverse >> simp[]) >>
        qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
        simp[asm_evm_rel_def] >> strip_tac >>
        gvs[asm_evm_rel_def]
      )
      (* Jump dest invalid: InvalidJumpDest ≠ StackOverflow *)
      >> (
        DISJ1_TAC >>
        match_mp_tac (Q.SPEC `InvalidJumpDest` handle_step_single_context |>
          SIMP_RULE (srw_ss()) [vfm_abort_def, exception_distinct]) >>
        simp[]
      )
    )
    (* Gas fail *)
    >> (
      DISJ1_TAC >>
      match_mp_tac (Q.SPEC `OutOfGas` handle_step_single_context |>
        SIMP_RULE (srw_ss()) [vfm_abort_def, exception_distinct]) >>
      simp[]
    )
  )
  (* === JUMPI === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_jumpi_def] >>
    Cases_on `as.as_stack` >> simp[] >>
    rename1 `(dest:bytes32) :: rest` >>
    Cases_on `rest` >> simp[] >>
    rename1 `dest :: (cond:bytes32) :: stk` >>
    (* EVM side: step_jumpi pops 2, sets jumpDest *)
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_jumpi_def, pop_stack_def,
         consume_gas_def, assert_def, LET_THM,
         set_jump_dest_def] >>
    fs[] >>
    (* Gas check *)
    IF_CASES_TAC >> simp[]
    (* Gas OK *)
    >- (
      (* Case split on cond = 0w: no-jump vs jump *)
      Cases_on `cond = 0w` >> simp[]
      (* cond = 0w: no jump, just increment PC *)
      >- (
        simp[inc_pc_or_jump_def, LET_THM,
             bind_def, get_current_context_def, return_def,
             set_current_context_def, is_call_def, opcode_def] >>
        qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
        simp[asm_evm_rel_def] >> strip_tac >>
        gvs[asm_evm_rel_def, asm_next_def, LET_THM] >>
        ONCE_REWRITE_TAC[GSYM arithmeticTheory.ADD1] >>
        simp[asm_pc_to_offset_suc, asm_inst_size_def]
      )
      (* cond <> 0w: jump case, same as JUMP *)
      >> (
        Cases_on `FLOOKUP (build_offset_to_pc prog) (w2n dest)` >> simp[] >>
        rename1 `FLOOKUP _ _ = SOME target_pc` >>
        simp[inc_pc_or_jump_def, LET_THM,
             bind_def, get_current_context_def, return_def,
             set_current_context_def, is_call_def, opcode_def,
             assert_def, ignore_bind_def] >>
        (* Jump dest validation IF *)
        IF_CASES_TAC >> simp[]
        (* Jump dest valid *)
        >- (
          `target_pc < LENGTH prog ∧
           asm_pc_to_offset prog target_pc = w2n dest` by (
            irule offset_to_pc_reverse >> simp[]) >>
          qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
          simp[asm_evm_rel_def] >> strip_tac >>
          gvs[asm_evm_rel_def]
        )
        (* Jump dest invalid *)
        >> (
          DISJ1_TAC >>
          match_mp_tac (Q.SPEC `InvalidJumpDest` handle_step_single_context |>
            SIMP_RULE (srw_ss()) [vfm_abort_def, exception_distinct]) >>
          simp[]
        )
      )
    )
    (* Gas fail *)
    >> (
      DISJ1_TAC >>
      match_mp_tac (Q.SPEC `OutOfGas` handle_step_single_context |>
        SIMP_RULE (srw_ss()) [vfm_abort_def, exception_distinct]) >>
      simp[]
    )
  )
  (* === JUMPDEST === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         step_inst_def, static_gas_def, consume_gas_def,
         set_current_context_def, assert_def] >>
    fs[] >> IF_CASES_TAC >> simp[] >>
    gas_close_tac
  )
  (* === STOP === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def, set_current_context_def,
         step_inst_def, set_return_data_def,
         finish_def, LET_THM] >>
    `handle_step NONE
       (es with contexts :=
         [(ctxt with returnData := [], rb)]) = (INR NONE,
       es with contexts :=
         [(ctxt with returnData := [], rb)])` by (
      irule handle_step_none_single_context >>
      qexistsl_tac [`ctxt with returnData := []`, `rb`] >>
      simp[] >> first_x_assum irule >> simp[]) >>
    simp[] >>
    (* simp resolves first disjunct (NONE ≠ SOME) to F, so no DISJ2_TAC needed *)
    qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
    simp[asm_evm_rel_def] >> strip_tac >>
    gvs[asm_evm_rel_def]
  )
  (* === RETURN === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_return_op_def, LET_THM] >>
    Cases_on `as.as_stack` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_return_def, pop_stack_def,
         consume_gas_def,
         memory_expansion_info_def, expand_memory_def,
         read_memory_def, set_return_data_def,
         finish_def,
         vfmConstantsTheory.word_size_def,
         assert_def, fail_def, LET_THM] >>
    rpt (IF_CASES_TAC >> gvs[]) >>
    (* Resolve handle_step NONE on gas-OK goals (conditional rewrite) *)
    simp[handle_step_none_single_context] >>
    (* Gas-fail: handle_step still present → gas_close_tac *)
    TRY gas_close_tac >>
    (* Gas-OK: disjunction resolved, just need asm_evm_rel *)
    qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
    simp[asm_evm_rel_def] >> strip_tac >>
    gvs[asm_evm_rel_def, asm_expand_memory_def, MAX_DEF] >>
    rpt (IF_CASES_TAC >> gvs[])
  )
  (* === REVERT === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[asm_revert_op_def, LET_THM] >>
    Cases_on `as.as_stack` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_return_def, pop_stack_def,
         consume_gas_def,
         memory_expansion_info_def, expand_memory_def,
         read_memory_def, set_return_data_def,
         revert_def,
         vfmConstantsTheory.word_size_def,
         assert_def, fail_def, LET_THM] >>
    rpt (IF_CASES_TAC >> gvs[]) >>
    (* Resolve handle_step (SOME Reverted) on gas-OK goals *)
    simp[handle_step_reverted_single_context] >>
    (* Gas-fail: handle_step still present → gas_close_tac *)
    TRY gas_close_tac >>
    (* Gas-OK: resolve asm_evm_rel *)
    qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
    simp[asm_evm_rel_def] >> strip_tac >>
    gvs[asm_evm_rel_def, asm_expand_memory_def, MAX_DEF] >>
    rpt (IF_CASES_TAC >> gvs[])
  )
  (* === INVALID === *)
  >- (
    identify_evm_op_tac >> gvs[] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def, set_current_context_def,
         step_inst_def, fail_def, LET_THM] >>
    DISJ1_TAC >>
    match_mp_tac (Q.SPEC `InvalidOpcode` handle_step_single_context |>
      SIMP_RULE (srw_ss()) [vfm_abort_def, exception_distinct]) >> simp[]
  )
QED

Theorem asm_evm_step_extcall_dispatch[local]:
  !prog as es name r.
    asm_wf prog /\ asm_evm_rel prog as es /\ LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit /\
    no_asm_calls prog /\
    asm_step_extcall name as = SOME r ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> StackOverflow) \/
    (case r of
       AsmOK as1 => ?es1. step es = (INL (), es1) /\
                           asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
     | AsmHalt as1 => ?es1. step es = (INR NONE, es1) /\ asm_evm_rel prog as1 es1
     | AsmRevert as1 => ?es1. step es = (INR (SOME Reverted), es1) /\
                               asm_evm_rel prog as1 es1
     | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\
                                  exc <> Reverted /\ asm_evm_rel prog as1 es1
     | AsmError _ => T)
Proof
  (* no_asm_calls excludes all extcall names (including SELFDESTRUCT).
     So asm_step_extcall returns NONE, contradicting SOME r. *)
  rpt gen_tac >> strip_tac >>
  `~is_evm_call_name name` by (
    fs[no_asm_calls_def] >>
    first_x_assum (qspecl_then [`as.as_pc`, `name`] mp_tac) >> simp[]) >>
  fs[is_evm_call_name_def, asm_step_extcall_def]
QED

(* TAKE n (REPLICATE m x) = REPLICATE n x when n <= m *)
Theorem take_replicate_le[local]:
  !n m (x:'a). n <= m ==> TAKE n (REPLICATE m x) = REPLICATE n x
Proof
  Induct_on `n` >> simp[] >> Cases_on `m` >> simp[]
QED

(* TAKE from zero-padded list = take_pad_0 *)
Theorem take_pad_replicate[local]:
  !n (l:byte list) k.
    n <= LENGTH l + k ==>
    TAKE n (l ++ REPLICATE k (0w:byte)) = take_pad_0 n l
Proof
  simp[vfmTypesTheory.take_pad_0_pad_take, PAD_RIGHT,
       GSYM rich_listTheory.REPLICATE_GENLIST] >>
  Induct_on `n` >> simp[] >> rpt strip_tac >>
  Cases_on `l` >> gvs[]
  >- (Cases_on `k` >> gvs[take_replicate_le])
  >> first_x_assum (qspecl_then [`t`, `k`] mp_tac) >> simp[]
QED

(* Key lemma: TAKE/DROP from expanded source = take_pad_0 from original *)
Theorem take_drop_expand_eq_pad[local]:
  !sz soff (src:byte list).
    TAKE sz (DROP soff (asm_expand_memory (soff + sz) src)) =
    take_pad_0 sz (DROP soff src)
Proof
  rpt gen_tac >> simp[asm_expand_memory_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `if rounded <= _ then _ else _` >>
  `soff + sz <= rounded` by
    (simp[Abbr `rounded`] >>
     mp_tac (Q.SPEC `soff + sz` n_le_round_up_32) >> simp[]) >>
  IF_CASES_TAC >| [
    (* rounded <= LENGTH src: src unchanged *)
    `soff + sz <= LENGTH src` by DECIDE_TAC >>
    simp[vfmTypesTheory.take_pad_0_def, PAD_RIGHT,
         GSYM rich_listTheory.REPLICATE_GENLIST,
         LENGTH_TAKE_EQ, LENGTH_DROP],
    (* rounded > LENGTH src: src expanded with zeros *)
    Cases_on `soff <= LENGTH src` >| [
      simp[DROP_APPEND1] >>
      match_mp_tac take_pad_replicate >>
      simp[LENGTH_DROP],
      `LENGTH src <= soff` by simp[] >>
      simp[DROP_APPEND2, rich_listTheory.DROP_REPLICATE,
           DROP_LENGTH_TOO_LONG,
           vfmTypesTheory.take_pad_0_def, PAD_RIGHT,
           GSYM rich_listTheory.REPLICATE_GENLIST] >>
      match_mp_tac take_replicate_le >>
      DECIDE_TAC
    ]
  ]
QED

Theorem asm_evm_step_copy_dispatch[local]:
  !prog as es name r.
    asm_wf prog /\ asm_evm_rel prog as es /\ LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit /\
    asm_step_copy name as = SOME r ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> StackOverflow) \/
    (case r of
       AsmOK as1 => ?es1. step es = (INL (), es1) /\
                           asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
     | AsmHalt as1 => ?es1. step es = (INR NONE, es1) /\ asm_evm_rel prog as1 es1
     | AsmRevert as1 => ?es1. step es = (INR (SOME Reverted), es1) /\
                               asm_evm_rel prog as1 es1
     | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\
                                  exc <> Reverted /\ asm_evm_rel prog as1 es1
     | AsmError _ => T)
Proof
  category_setup_tac >>
  qpat_x_assum `asm_step_copy _ _ = SOME _` mp_tac >>
  simp[asm_step_copy_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[] >>
  identify_evm_op_tac >> gvs[] >|
  [
  (* === CALLDATACOPY === *)
  simp[asm_copy_to_mem_def, LET_THM] >>
  Cases_on `as.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def,
       set_current_context_def,
       step_inst_def, step_copy_to_memory_def,
       copy_to_memory_def, pop_stack_def,
       consume_gas_def,
       memory_expansion_info_def, expand_memory_def,
       write_memory_def,
       vfmConstantsTheory.word_size_def,
       vfmConstantsTheory.memory_copy_cost_def,
       get_call_data_def,
       assert_def, fail_def, LET_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  (* gas-fail: handle_step resolves *)
  TRY (
    DISJ1_TAC >>
    FIRST (map (fn exc =>
      match_mp_tac (Q.SPEC exc handle_step_single_context |>
        SIMP_RULE (srw_ss()) [vfm_abort_def, exception_distinct]) >>
      simp[])
    [`OutOfGas`, `WriteInStaticContext`, `StackUnderflow`]) >> NO_TAC
  ) >>
  (* Gas-OK: prove asm_evm_rel *)
  DISJ2_TAC >>
  simp[inc_pc_or_jump_def, LET_THM, opcode_def,
       bind_def, get_current_context_def, return_def,
       set_current_context_def, is_call_def] >>
  qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
  simp[asm_evm_rel_def] >> strip_tac >>
  gvs[asm_evm_rel_def, asm_next_def, LET_THM] >>
  ONCE_REWRITE_TAC[GSYM arithmeticTheory.ADD1] >>
  simp[asm_pc_to_offset_suc, asm_inst_size_def] >>
  (* Memory and source bytes equivalence *)
  simp[take_drop_expand_eq_pad, asm_expand_eq_evm_simp,
       vfmTypesTheory.take_pad_0_0, vfmTypesTheory.LENGTH_take_pad_0] >>
  simp[asm_expand_memory_def, LET_THM, MAX_DEF] >>
  rpt (IF_CASES_TAC >> gvs[])
  ,
  (* === RETURNDATACOPY === *)
  simp[asm_returndatacopy_def, LET_THM] >>
  Cases_on `as.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  (* Split on ASM OOB check FIRST *)
  IF_CASES_TAC >> gvs[]
  >- (
    (* OOB: r = AsmFault. All EVM outcomes give DISJ1 (some exception) *)
    DISJ1_TAC >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def,
         set_current_context_def,
         step_inst_def, step_return_data_copy_def,
         step_copy_to_memory_def,
         copy_to_memory_def, pop_stack_def,
         consume_gas_def,
         memory_expansion_info_def, expand_memory_def,
         write_memory_def,
         vfmConstantsTheory.word_size_def,
         vfmConstantsTheory.memory_copy_cost_def,
         get_return_data_check_def, get_return_data_def,
         assert_def, fail_def, LET_THM] >>
    rpt (IF_CASES_TAC >> gvs[]) >>
    FIRST (map (fn exc =>
      match_mp_tac (Q.SPEC exc handle_step_single_context |>
        SIMP_RULE (srw_ss()) [vfm_abort_def, exception_distinct]) >>
      simp[])
    [`OutOfGas`, `WriteInStaticContext`, `StackUnderflow`,
     `OutOfBoundsRead`])
  ) >>
  (* In-bounds case: same pattern as CALLDATACOPY *)
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def,
       set_current_context_def,
       step_inst_def, step_return_data_copy_def,
       step_copy_to_memory_def,
       copy_to_memory_def, pop_stack_def,
       consume_gas_def,
       memory_expansion_info_def, expand_memory_def,
       write_memory_def,
       vfmConstantsTheory.word_size_def,
       vfmConstantsTheory.memory_copy_cost_def,
       get_return_data_check_def, get_return_data_def,
       assert_def, fail_def, LET_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  TRY (
    DISJ1_TAC >>
    FIRST (map (fn exc =>
      match_mp_tac (Q.SPEC exc handle_step_single_context |>
        SIMP_RULE (srw_ss()) [vfm_abort_def, exception_distinct]) >>
      simp[])
    [`OutOfGas`, `WriteInStaticContext`, `StackUnderflow`,
     `OutOfBoundsRead`]) >> NO_TAC
  ) >>
  (* Gas-OK, in-bounds: bytes match exactly *)
  DISJ2_TAC >>
  simp[inc_pc_or_jump_def, LET_THM, opcode_def,
       bind_def, get_current_context_def, return_def,
       set_current_context_def, is_call_def] >>
  qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
  simp[asm_evm_rel_def] >> strip_tac >>
  gvs[asm_evm_rel_def, asm_next_def, LET_THM,
       vfmTypesTheory.LENGTH_take_pad_0] >>
  ONCE_REWRITE_TAC[GSYM arithmeticTheory.ADD1] >>
  simp[asm_pc_to_offset_suc, asm_inst_size_def] >>
  simp[vfmTypesTheory.take_pad_0_def, PAD_RIGHT,
       GSYM rich_listTheory.REPLICATE_GENLIST,
       LENGTH_TAKE_EQ, LENGTH_DROP] >>
  simp[asm_expand_memory_def, LET_THM, MAX_DEF] >>
  rpt (IF_CASES_TAC >> gvs[])
  ,
  (* === CODECOPY === same pattern as CALLDATACOPY *)
  simp[asm_copy_to_mem_def, LET_THM] >>
  Cases_on `as.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def,
       set_current_context_def,
       step_inst_def, step_copy_to_memory_def,
       copy_to_memory_def, pop_stack_def,
       consume_gas_def,
       memory_expansion_info_def, expand_memory_def,
       write_memory_def,
       vfmConstantsTheory.word_size_def,
       vfmConstantsTheory.memory_copy_cost_def,
       get_current_code_def,
       assert_def, fail_def, LET_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  TRY (
    DISJ1_TAC >>
    FIRST (map (fn exc =>
      match_mp_tac (Q.SPEC exc handle_step_single_context |>
        SIMP_RULE (srw_ss()) [vfm_abort_def, exception_distinct]) >>
      simp[])
    [`OutOfGas`, `WriteInStaticContext`, `StackUnderflow`]) >> NO_TAC
  ) >>
  DISJ2_TAC >>
  simp[inc_pc_or_jump_def, LET_THM, opcode_def,
       bind_def, get_current_context_def, return_def,
       set_current_context_def, is_call_def] >>
  qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
  simp[asm_evm_rel_def] >> strip_tac >>
  gvs[asm_evm_rel_def, asm_next_def, LET_THM] >>
  ONCE_REWRITE_TAC[GSYM arithmeticTheory.ADD1] >>
  simp[asm_pc_to_offset_suc, asm_inst_size_def] >>
  simp[take_drop_expand_eq_pad, asm_expand_eq_evm_simp,
       vfmTypesTheory.take_pad_0_0, vfmTypesTheory.LENGTH_take_pad_0] >>
  simp[asm_expand_memory_def, LET_THM, MAX_DEF] >>
  rpt (IF_CASES_TAC >> gvs[])
  ,
  (* === EXTCODECOPY === 4 stack args + access_address *)
  simp[asm_extcodecopy_def, LET_THM] >>
  Cases_on `as.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  (* 3 elements on stack so far; case on t'' for the 4th *)
  rename1 `h :: h' :: h'' :: rest` >>
  Cases_on `rest` >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def,
       set_current_context_def,
       step_inst_def, step_ext_code_copy_def,
       step_copy_to_memory_def,
       copy_to_memory_def, pop_stack_def,
       consume_gas_def,
       memory_expansion_info_def, expand_memory_def,
       write_memory_def,
       vfmConstantsTheory.word_size_def,
       vfmConstantsTheory.memory_copy_cost_def,
       get_code_def, get_accounts_def,
       access_address_def, domain_check_def, set_domain_def,
       assert_def, fail_def, LET_THM] >>
  (* Domain check: split on msdomain *)
  TRY (Cases_on `es.msdomain` >> simp[]) >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  (* gas-fail + abort errors *)
  TRY (
    DISJ1_TAC >>
    FIRST (map (fn exc =>
      match_mp_tac (Q.SPEC exc handle_step_single_context |>
        SIMP_RULE (srw_ss()) [vfm_abort_def, exception_distinct]) >>
      simp[])
    [`OutOfGas`, `WriteInStaticContext`, `StackUnderflow`]) >> NO_TAC
  ) >>
  TRY (
    DISJ1_TAC >>
    simp[handle_step_def, reraise_def, vfm_abort_def] >>
    simp[exception_distinct, exception_11] >> NO_TAC
  ) >>
  (* Gas-OK *)
  DISJ2_TAC >>
  simp[inc_pc_or_jump_def, LET_THM, opcode_def,
       bind_def, get_current_context_def, return_def,
       set_current_context_def, is_call_def] >>
  qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
  simp[asm_evm_rel_def] >> strip_tac >>
  gvs[asm_evm_rel_def, asm_next_def, LET_THM,
       vfmTypesTheory.LENGTH_take_pad_0] >>
  ONCE_REWRITE_TAC[GSYM arithmeticTheory.ADD1] >>
  simp[asm_pc_to_offset_suc, asm_inst_size_def] >>
  simp[take_drop_expand_eq_pad, asm_expand_eq_evm_simp,
       vfmTypesTheory.take_pad_0_0] >>
  simp[asm_expand_memory_def, LET_THM, MAX_DEF] >>
  rpt (IF_CASES_TAC >> gvs[])
  ]
QED

Theorem asm_evm_step_context_dispatch[local]:
  !prog as es name r.
    asm_wf prog /\ asm_evm_rel prog as es /\ LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit /\
    asm_step_context name as = SOME r ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> StackOverflow) \/
    (case r of
       AsmOK as1 => ?es1. step es = (INL (), es1) /\
                           asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
     | AsmHalt as1 => ?es1. step es = (INR NONE, es1) /\ asm_evm_rel prog as1 es1
     | AsmRevert as1 => ?es1. step es = (INR (SOME Reverted), es1) /\
                               asm_evm_rel prog as1 es1
     | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\
                                  exc <> Reverted /\ asm_evm_rel prog as1 es1
     | AsmError _ => T)
Proof
  category_setup_tac >>
  qpat_x_assum `asm_step_context _ _ = SOME _` mp_tac >>
  simp[asm_step_context_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[] >>
  identify_evm_op_tac >> gvs[] >>
  FIRST [
    (* push_val ops: guard on asm_push_val in goal *)
    (fn (asl, g) =>
      if can (find_term (can (match_term ``asm_push_val v s``))) g
      then ALL_TAC (asl, g)
      else raise (mk_HOL_ERR "" "" "not push_val")) >>
    simp[asm_push_val_def, asm_next_def] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def, set_current_context_def,
         step_inst_def, step_msgParams_def, step_context_def,
         step_txParams_def, get_tx_params_def,
         step_self_balance_def, get_accounts_def, get_callee_def,
         push_stack_def, consume_gas_def, assert_def, LET_THM] >>
    fs[] >> IF_CASES_TAC >> simp[] >>
    gas_close_tac,
    (* state_unop ops: guard on asm_state_unop in goal *)
    (fn (asl, g) =>
      if can (find_term (can (match_term ``asm_state_unop f s``))) g
      then ALL_TAC (asl, g)
      else raise (mk_HOL_ERR "" "" "not state_unop")) >>
    simp[asm_state_unop_def, asm_next_def] >>
    Cases_on `as.as_stack` >> gvs[] >>
    simp[step_def, handle_def, bind_def, ignore_bind_def,
         get_current_context_def, return_def, set_current_context_def,
         step_inst_def, step_call_data_load_def,
         step_block_hash_def, step_blob_hash_def,
         step_balance_def, step_ext_code_size_def, step_ext_code_hash_def,
         pop_stack_def, push_stack_def, consume_gas_def,
         get_accounts_def, get_call_data_def, get_tx_params_def,
         access_address_def, domain_check_def, set_domain_def,
         get_callee_def, fail_def,
         assert_def, LET_THM] >>
    (* For access_address ops: split on domain type first *)
    TRY (Cases_on `es.msdomain` >> simp[]) >>
    (* Resolve all if-then-else, preserving disjunction for gas_close_tac *)
    fs[] >> rpt (IF_CASES_TAC >> simp[]) >>
    (* gas_close_tac handles: gas-fail, abort errors, gas-OK.
       For inconsistent IF splits (blobhash/blockhash conditions),
       gas-OK branch detects contradiction after asm_evm_rel unfold. *)
    gas_close_tac
  ]
QED

Theorem asm_evm_step_dup_dispatch[local]:
  !prog as es name n r.
    asm_wf prog /\ asm_evm_rel prog as es /\ LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit /\
    ALOOKUP dup_table name = SOME n /\
    r = asm_dup n as ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> StackOverflow) \/
    (case r of
       AsmOK as1 => ?es1. step es = (INL (), es1) /\
                           asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
     | AsmHalt as1 => ?es1. step es = (INR NONE, es1) /\ asm_evm_rel prog as1 es1
     | AsmRevert as1 => ?es1. step es = (INR (SOME Reverted), es1) /\
                               asm_evm_rel prog as1 es1
     | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\
                                  exc <> Reverted /\ asm_evm_rel prog as1 es1
     | AsmError _ => T)
Proof
  category_setup_tac >>
  qpat_x_assum `ALOOKUP dup_table _ = SOME _` mp_tac >>
  simp[dup_table_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[] >>
  identify_evm_op_tac >> gvs[] >>
  simp[asm_dup_def, asm_next_def] >>
  IF_CASES_TAC >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, step_dup_def,
       consume_gas_def, push_stack_def, assert_def, LET_THM] >>
  fs[] >> IF_CASES_TAC >> simp[] >>
  gas_close_tac
QED

(* Helper: LUPDATE as TAKE/DROP *)
Theorem lupdate_take_drop[local]:
  !n v l. n < LENGTH l ==> (LUPDATE v n l = TAKE n l ++ [v] ++ DROP (SUC n) l)
Proof
  Induct_on `n` >> Cases_on `l` >> simp[LUPDATE_def]
QED

(* Helper: double-LUPDATE swap = TAKE/DROP swap (using TL form for EL 0 = HD simp) *)
Theorem swap_lupdate_eq[local]:
  !n stk. 0 < n /\ n < LENGTH stk ==>
    (LUPDATE (HD stk) n (LUPDATE (EL n stk) 0 stk) =
     EL (n - 1) (TL stk) :: TAKE (n - 1) (TL stk) ++ [HD stk] ++ DROP n (TL stk))
Proof
  Cases_on `n` >> simp[] >>
  Cases_on `stk` >> simp[LUPDATE_def, lupdate_take_drop]
QED

Theorem asm_evm_step_swap_dispatch[local]:
  !prog as es name n r.
    asm_wf prog /\ asm_evm_rel prog as es /\ LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit /\
    ALOOKUP swap_table name = SOME n /\
    r = asm_swap n as ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> StackOverflow) \/
    (case r of
       AsmOK as1 => ?es1. step es = (INL (), es1) /\
                           asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
     | AsmHalt as1 => ?es1. step es = (INR NONE, es1) /\ asm_evm_rel prog as1 es1
     | AsmRevert as1 => ?es1. step es = (INR (SOME Reverted), es1) /\
                               asm_evm_rel prog as1 es1
     | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\
                                  exc <> Reverted /\ asm_evm_rel prog as1 es1
     | AsmError _ => T)
Proof
  category_setup_tac >>
  qpat_x_assum `ALOOKUP swap_table _ = SOME _` mp_tac >>
  simp[swap_table_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[] >>
  identify_evm_op_tac >> gvs[] >>
  simp[asm_swap_def, asm_next_def] >>
  IF_CASES_TAC >> gvs[] >>
  simp[swap_lupdate_eq] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, set_current_context_def,
       step_inst_def, step_swap_def,
       consume_gas_def, assert_def, LET_THM] >>
  fs[] >> IF_CASES_TAC >> simp[] >>
  gas_close_tac
QED

Theorem asm_evm_step_log_dispatch[local]:
  !prog as es name n r.
    asm_wf prog /\ asm_evm_rel prog as es /\ LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp name /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit /\
    ALOOKUP log_table name = SOME n /\
    r = asm_log n as ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> StackOverflow) \/
    (case r of
       AsmOK as1 => ?es1. step es = (INL (), es1) /\
                           asm_evm_rel prog as1 es1 /\ LENGTH es1.contexts = 1
     | AsmHalt as1 => ?es1. step es = (INR NONE, es1) /\ asm_evm_rel prog as1 es1
     | AsmRevert as1 => ?es1. step es = (INR (SOME Reverted), es1) /\
                               asm_evm_rel prog as1 es1
     | AsmFault as1 => ?es1 exc. step es = (INR (SOME exc), es1) /\
                                  exc <> Reverted /\ asm_evm_rel prog as1 es1
     | AsmError _ => T)
Proof
  category_setup_tac >>
  qpat_x_assum `ALOOKUP log_table _ = SOME _` mp_tac >>
  simp[log_table_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> strip_tac >> gvs[] >>
  identify_evm_op_tac >> gvs[] >>
  simp[asm_log_def, LET_THM] >>
  IF_CASES_TAC >> gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def,
       set_current_context_def,
       step_inst_def, step_log_def, pop_stack_def,
       consume_gas_def, push_stack_def,
       memory_expansion_info_def, expand_memory_def,
       read_memory_def, push_logs_def,
       get_callee_def, get_static_def,
       assert_not_static_def,
       vfmConstantsTheory.word_size_def,
       vfmConstantsTheory.log_topic_cost_def,
       vfmConstantsTheory.log_data_cost_def,
       assert_def, fail_def, LET_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  (* gas-fail / static-fail: handle_step resolves *)
  TRY (
    DISJ1_TAC >>
    FIRST (map (fn exc =>
      match_mp_tac (Q.SPEC exc handle_step_single_context |>
        SIMP_RULE (srw_ss()) [vfm_abort_def, exception_distinct]) >>
      simp[])
    [`OutOfGas`, `WriteInStaticContext`, `StackUnderflow`]) >> NO_TAC
  ) >>
  (* gas-OK: inc_pc_or_jump resolves, then asm_evm_rel *)
  DISJ2_TAC >>
  simp[inc_pc_or_jump_def, LET_THM, opcode_def,
       bind_def, get_current_context_def, return_def,
       set_current_context_def, is_call_def] >>
  qpat_x_assum `asm_evm_rel _ _ _` mp_tac >>
  simp[asm_evm_rel_def] >> strip_tac >>
  gvs[asm_evm_rel_def, asm_next_def, LET_THM,
      asm_expand_memory_def, MAX_DEF, EL_TAKE, HD_TAKE, DROP_TAKE] >>
  rpt (IF_CASES_TAC >> gvs[EL_TAKE, HD_TAKE, DROP_TAKE]) >>
  ONCE_REWRITE_TAC[GSYM arithmeticTheory.ADD1] >>
  simp[asm_pc_to_offset_suc, asm_inst_size_def]
QED

(* ===== Push-style helpers (AsmPush, AsmPushLabel, AsmPushOfst) ===== *)

(* AsmPush bytes: directly push word_of_bytes F 0w (REVERSE bytes) *)
Theorem asm_evm_step_push[local]:
  !prog as es bytes.
    asm_wf prog /\
    asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmPush bytes /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               exc <> StackOverflow) \/
    ?es1. step es = (INL (), es1) /\
          asm_evm_rel prog
            (asm_next (as with as_stack :=
              word_of_bytes F 0w (REVERSE bytes) :: as.as_stack)) es1 /\
          LENGTH es1.contexts = 1
Proof
  rpt strip_tac >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  Cases_on `bytes`
  (* empty case: Push 0 [] *)
  >- (mp_tac (Q.SPECL [`prog`, `as`, `es`, `Push 0 []`,
        `word_of_bytes F (0w:bytes32) (REVERSE ([]:(word8 list)))`, `2`]
        evm_push_step) >>
      simp[encode_inst_def, opcode_def, step_inst_def, step_push_def,
           wf_opname_def, is_call_def, static_gas_def,
           wordsTheory.WORD_ADD_0])
  (* non-empty case: Push (SUC (LENGTH t)) (h::t) *)
  >> rename1 `AsmPush (h::t)` >>
     `encoding_wf_inst (EL as.as_pc prog) (SND (compute_label_offsets prog))`
       by (irule asm_encoding_wf_el >> fs[asm_wf_def]) >>
     gvs[encoding_wf_inst_def] >>
     mp_tac (Q.SPECL [`prog`, `as`, `es`,
       `Push (SUC (LENGTH t)) (h::t)`,
       `word_of_bytes F (0w:bytes32) (REVERSE (h::t))`,
       `3`] evm_push_step) >>
     impl_tac
     >- simp[encode_inst_def, opcode_def, step_inst_def, step_push_def,
             wf_opname_def, is_call_def, static_gas_def,
             GSYM wordsTheory.word_add_n2w]
     >> simp[]
QED

(* AsmPushLabel lbl: push n2w off where off = FLOOKUP offsets lbl *)
Theorem asm_evm_step_pushlabel[local]:
  !prog as es lbl off.
    asm_wf prog /\
    asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmPushLabel lbl /\
    FLOOKUP (SND (compute_label_offsets prog)) lbl = SOME off /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               exc <> StackOverflow) \/
    ?es1. step es = (INL (), es1) /\
          asm_evm_rel prog
            (asm_next (as with as_stack := n2w off :: as.as_stack)) es1 /\
          LENGTH es1.contexts = 1
Proof
  rpt strip_tac >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  `encoding_wf_inst (EL as.as_pc prog) (SND (compute_label_offsets prog))`
    by (irule asm_encoding_wf_el >> fs[asm_wf_def]) >>
  `LENGTH (encode_num_bytes off) <= symbol_size` by
    (fs[encoding_wf_inst_def] >> res_tac >> simp[]) >>
  mp_tac (Q.SPECL [`prog`, `as`, `es`,
    `Push symbol_size (pad_bytes symbol_size (encode_num_bytes off))`,
    `word_of_bytes F (0w:bytes32)
       (REVERSE (pad_bytes symbol_size (encode_num_bytes off)))`,
    `3`] evm_push_step) >>
  impl_tac
  >- simp[encode_inst_def, opcode_def, step_inst_def, step_push_def,
          wf_opname_def, is_call_def, static_gas_def, symbol_size_def,
          pad_bytes_length, LET_THM, wordsTheory.word_add_n2w]
  >> simp[pad_encode_bytes32]
QED

(* AsmPushOfst lbl delta: push n2w (off + delta) *)
Theorem asm_evm_step_pushofst[local]:
  !prog as es lbl delta off.
    asm_wf prog /\
    asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmPushOfst lbl delta /\
    FLOOKUP (SND (compute_label_offsets prog)) lbl = SOME off /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               exc <> StackOverflow) \/
    ?es1. step es = (INL (), es1) /\
          asm_evm_rel prog
            (asm_next (as with as_stack :=
              n2w (off + delta) :: as.as_stack)) es1 /\
          LENGTH es1.contexts = 1
Proof
  rpt strip_tac >>
  `~is_data_inst (EL as.as_pc prog)` by simp[is_data_inst_def] >>
  `encoding_wf_inst (EL as.as_pc prog) (SND (compute_label_offsets prog))`
    by (irule asm_encoding_wf_el >> fs[asm_wf_def]) >>
  `LENGTH (encode_num_bytes (off + delta)) <= symbol_size` by
    (fs[encoding_wf_inst_def] >> res_tac >> simp[]) >>
  mp_tac (Q.SPECL [`prog`, `as`, `es`,
    `Push symbol_size
       (pad_bytes symbol_size (encode_num_bytes (off + delta)))`,
    `word_of_bytes F (0w:bytes32)
       (REVERSE (pad_bytes symbol_size (encode_num_bytes (off + delta))))`,
    `3`] evm_push_step) >>
  impl_tac
  >- simp[encode_inst_def, opcode_def, step_inst_def, step_push_def,
          wf_opname_def, is_call_def, static_gas_def, symbol_size_def,
          pad_bytes_length, LET_THM, wordsTheory.word_add_n2w]
  >> simp[pad_encode_bytes32]
QED

(* ===== Main theorem ===== *)

Theorem asm_evm_step:
  !prog as es.
    asm_wf prog /\
    asm_evm_rel prog as es /\
    LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\
    ~is_data_inst (EL as.as_pc prog) /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    LENGTH as.as_stack < stack_limit /\
    no_asm_calls prog /\
    (!i. i < LENGTH prog ==> 0 < asm_inst_size (EL i prog)) ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               exc <> StackOverflow) \/
    (case asm_step (SND (compute_label_offsets prog))
                   (build_offset_to_pc prog)
                   (EL as.as_pc prog) as of
       AsmOK as1 =>
         ?es1. step es = (INL (), es1) /\
               asm_evm_rel prog as1 es1 /\
               LENGTH es1.contexts = 1
     | AsmHalt as1 =>
         ?es1. step es = (INR NONE, es1) /\
               asm_evm_rel prog as1 es1
     | AsmRevert as1 =>
         ?es1. step es = (INR (SOME Reverted), es1) /\
               asm_evm_rel prog as1 es1
     | AsmFault as1 =>
         ?es1 exc. step es = (INR (SOME exc), es1) /\
                   exc <> Reverted /\ asm_evm_rel prog as1 es1
     | AsmError _ => T)
Proof
  rpt strip_tac >>
  Cases_on `EL as.as_pc prog` >> gvs[asm_step_def, is_data_inst_def]
  (* AsmOp name *)
  >- (rename1 `AsmOp name` >>
      simp[asm_step_op_def] >>
      reverse (Cases_on `asm_step_arith name as`) >> simp[]
      >- (match_mp_tac asm_evm_step_arith_dispatch >>
          simp[] >> gvs[is_data_inst_def] >> metis_tac[])
      >> reverse (Cases_on `asm_step_compare name as`) >> simp[]
      >- (match_mp_tac asm_evm_step_compare_dispatch >>
          simp[] >> gvs[is_data_inst_def] >> metis_tac[])
      >> reverse (Cases_on `asm_step_bitwise name as`) >> simp[]
      >- (match_mp_tac asm_evm_step_bitwise_dispatch >>
          simp[] >> gvs[is_data_inst_def] >> metis_tac[])
      >> reverse (Cases_on `asm_step_memory name as`) >> simp[]
      >- (match_mp_tac asm_evm_step_memory_dispatch >>
          simp[] >> gvs[is_data_inst_def] >> metis_tac[])
      >> reverse (Cases_on `asm_step_control (build_offset_to_pc prog) name as`) >> simp[]
      >- (match_mp_tac asm_evm_step_control_dispatch >>
          simp[] >> gvs[is_data_inst_def] >> metis_tac[])
      >> reverse (Cases_on `asm_step_extcall name as`) >> simp[]
      >- (match_mp_tac asm_evm_step_extcall_dispatch >>
          simp[is_data_inst_def, no_asm_calls_def] >> metis_tac[])
      >> reverse (Cases_on `asm_step_copy name as`) >> simp[]
      >- (match_mp_tac asm_evm_step_copy_dispatch >>
          simp[] >> gvs[is_data_inst_def] >> metis_tac[])
      >> reverse (Cases_on `asm_step_context name as`) >> simp[]
      >- (match_mp_tac asm_evm_step_context_dispatch >>
          simp[] >> gvs[is_data_inst_def] >> metis_tac[])
      >> reverse (Cases_on `ALOOKUP dup_table name`) >> simp[]
      >- (match_mp_tac asm_evm_step_dup_dispatch >>
          simp[] >> gvs[is_data_inst_def] >> metis_tac[])
      >> reverse (Cases_on `ALOOKUP swap_table name`) >> simp[]
      >- (match_mp_tac asm_evm_step_swap_dispatch >>
          simp[] >> gvs[is_data_inst_def] >> metis_tac[])
      >> reverse (Cases_on `ALOOKUP log_table name`) >> simp[]
      >- (match_mp_tac asm_evm_step_log_dispatch >>
          simp[] >> gvs[is_data_inst_def] >> metis_tac[])
      >> simp[]
     )
  (* AsmPush *)
  >- (rename1 `AsmPush bytes` >> simp[] >>
      irule asm_evm_step_push >> simp[])
  (* AsmPushLabel *)
  >- (rename1 `AsmPushLabel lbl` >>
      Cases_on `FLOOKUP (SND (compute_label_offsets prog)) lbl` >> simp[]
      >> rename1 `SOME off` >>
      irule asm_evm_step_pushlabel >> simp[])
  (* AsmPushOfst *)
  >- (rename1 `AsmPushOfst lbl delta` >>
      Cases_on `FLOOKUP (SND (compute_label_offsets prog)) lbl` >> simp[]
      >> rename1 `SOME off` >>
      ONCE_REWRITE_TAC[arithmeticTheory.ADD_COMM] >>
      irule asm_evm_step_pushofst >> simp[])
  (* AsmLabel *)
  >- (rename1 `AsmLabel lbl` >> simp[] >>
      irule asm_evm_step_label >> simp[])
QED

(* ===== asm_steps chaining ===== *)

(* When asm_steps (SUC n) steps, it first does one step then n more *)
Theorem asm_steps_suc:
  !label_offsets offset_to_pc prog n as.
    asm_steps label_offsets offset_to_pc prog (SUC n) as =
      if as.as_pc >= LENGTH prog then AsmError "pc out of bounds"
      else
        case asm_step label_offsets offset_to_pc
               (EL as.as_pc prog) as of
          AsmOK as1 =>
            asm_steps label_offsets offset_to_pc prog n as1
        | other => other
Proof
  rw[asm_steps_def]
QED

(* The asm_steps reachability condition propagates through one step *)
Theorem asm_steps_reach_step:
  !label_offsets offset_to_pc prog n as as1.
    asm_step label_offsets offset_to_pc (EL as.as_pc prog) as =
      AsmOK as1 /\
    as.as_pc < LENGTH prog /\
    LENGTH as.as_stack < stack_limit ==>
    (!m as2. m <= n /\
             asm_steps label_offsets offset_to_pc prog m as1 = AsmOK as2 ==>
             LENGTH as2.as_stack < stack_limit) ==>
    (!m as2. m <= SUC n /\
             asm_steps label_offsets offset_to_pc prog m as = AsmOK as2 ==>
             LENGTH as2.as_stack < stack_limit)
Proof
  rw[] >> Cases_on `m`
  >- (gvs[asm_steps_def])
  >> rename1 `SUC m1 <= SUC n` >>
     gvs[asm_steps_def] >>
     first_x_assum (qspecl_then [`m1`, `as2`] mp_tac) >> simp[]
QED
