Theory lowerDloadNormalDispatch
Ancestors
  lowerDloadNormalExisting lowerDloadResidualNonmemory
  lowerDloadResidualImmutable lowerDloadResidualCopy lowerDloadResidualRead
  lowerDloadNormalOffset
  venomWf venomInst list

(* Shape-only boundary for the literal parameter families.  In particular,
   PARAM does not require the entry parameter vector to match AP in length. *)
Theorem ld_normal_parameter_shape:
  inst_wf i /\ MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM] ==>
  ?idx out. i.inst_operands = [Lit idx] /\ i.inst_outputs = [out]
Proof
  strip_tac >>
  qpat_x_assum `inst_wf i` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
  simp[MEM] >> strip_tac >>
  simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]
QED

(* The memory operands of LOG are the last two elements of its tail,
   not the first two.  The count condition supplies the needed lower bound. *)
Theorem ld_normal_log_shape:
  inst_wf i /\ i.inst_opcode = LOG ==>
  ?tc off sz topics.
    i.inst_operands = Lit tc :: REVERSE (off::sz::topics) /\
    LENGTH topics = w2n tc /\ i.inst_outputs = []
Proof
  strip_tac >> gvs[inst_wf_def] >>
  rename1 `i.inst_operands = Lit tc :: rest` >>
  `2 <= LENGTH (REVERSE rest)` by simp[] >>
  Cases_on `REVERSE rest` >> gvs[] >>
  rename1 `REVERSE rest = off :: tail` >>
  Cases_on `tail` >> gvs[] >>
  rename1 `REVERSE rest = off :: sz :: topics` >>
  qexistsl_tac [`off`, `sz`, `topics`] >>
  conj_tac >-
    (qpat_x_assum `REVERSE rest = _`
       (mp_tac o CONV_RULE (LAND_CONV (REWR_CONV REVERSE_REVERSE)) o
        AP_TERM ``REVERSE : operand list -> operand list``) >> simp[]) >>
  `LENGTH (REVERSE rest) = LENGTH (off::sz::topics)` by metis_tac[] >>
  fs[]
QED

(* Exhaustive partition for the ordinary normal-data dispatcher below.
   The complement retains its separate control/call/allocation/effect owners. *)
Theorem ld_normal_opcode_partition:
  ~MEM opc
    [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR;
     SIGNEXTEND; BYTE; MLOAD; MSTORE; MSTORE8; MCOPY; SLOAD; SSTORE;
     TLOAD; TSTORE; ILOAD; ISTORE; PARAM; RETPC_PARAM; ASSIGN; NOP;
     INITIAL_FMP; BUMP; CALLER; CALLVALUE; CALLDATALOAD; CALLDATASIZE;
     CALLDATACOPY; ADDRESS; ORIGIN; GASPRICE; GAS; GASLIMIT; COINBASE;
     TIMESTAMP; NUMBER; PREVRANDAO; CHAINID; SELFBALANCE; BALANCE;
     BLOCKHASH; BASEFEE; CODESIZE; CODECOPY; EXTCODESIZE; EXTCODEHASH;
     EXTCODECOPY; RETURNDATASIZE; RETURNDATACOPY; BLOBHASH; BLOBBASEFEE;
     SHA3; LOG; ASSERT; ASSERT_UNREACHABLE; OFFSET] <=>
  MEM opc [MEMTOP; JMP; JNZ; DJMP; RET; RETURN; REVERT; STOP; SINK;
    PHI; ALLOCA; DALLOCA; DRET; GETFMP; SETFMP; RETFMP; INVOKE;
    FMP_PARAM; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2;
    SELFDESTRUCT; INVALID; DLOAD; DLOADBYTES]
Proof
  Cases_on `opc` >> simp[]
QED

Theorem ld_normal_ordinary_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\ ld_stack_origin vs0 CS stk fn s0 /\
  LIST_REL (\A g. FINITE A /\
    CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
    (A::suspended) (fn::MAP (\f. f.cf_fn) stk) /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  ~in_revert_forward fn s /\
  MEM i.inst_opcode
    [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR;
     SIGNEXTEND; BYTE; MLOAD; MSTORE; MSTORE8; MCOPY; SLOAD; SSTORE;
     TLOAD; TSTORE; ILOAD; ISTORE; PARAM; RETPC_PARAM; ASSIGN; NOP;
     INITIAL_FMP; BUMP; CALLER; CALLVALUE; CALLDATALOAD; CALLDATASIZE;
     CALLDATACOPY; ADDRESS; ORIGIN; GASPRICE; GAS; GASLIMIT; COINBASE;
     TIMESTAMP; NUMBER; PREVRANDAO; CHAINID; SELFBALANCE; BALANCE;
     BLOCKHASH; BASEFEE; CODESIZE; CODECOPY; EXTCODESIZE; EXTCODEHASH;
     EXTCODECOPY; RETURNDATASIZE; RETURNDATACOPY; BLOBHASH; BLOBBASEFEE;
     SHA3; LOG; ASSERT; ASSERT_UNREACHABLE; OFFSET] /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f

Proof
  strip_tac >>
  `inst_wf i` by (drule_all ld_annotated_inst_wf >> simp[]) >>
  Cases_on `MEM i.inst_opcode
    [MUL;Div;Mod;SDIV;SMOD;Exp;ADDMOD;MULMOD;SLT;SGT;ISZERO;AND;OR;XOR;NOT]`
  >- suspend "scalar" >>
  Cases_on `i.inst_opcode = ASSIGN` >- suspend "assign" >>
  Cases_on `MEM i.inst_opcode [PARAM;RETPC_PARAM]` >- suspend "param" >>
  Cases_on `MEM i.inst_opcode [ADD;SUB]` >- suspend "affine" >>
  Cases_on `MEM i.inst_opcode [SHL;SHR;SAR]` >- suspend "shift" >>
  Cases_on `MEM i.inst_opcode [EQ;LT;GT]` >- suspend "compare" >>
  Cases_on `i.inst_opcode = MLOAD` >- suspend "mload" >>
  Cases_on `i.inst_opcode = ILOAD` >- suspend "iload" >>
  Cases_on `i.inst_opcode = MSTORE` >- suspend "mstore" >>
  Cases_on `i.inst_opcode = MSTORE8` >- suspend "mstore8" >>
  Cases_on `i.inst_opcode = ISTORE` >- suspend "istore" >>
  Cases_on `i.inst_opcode = MCOPY` >- suspend "mcopy" >>
  Cases_on `MEM i.inst_opcode [CALLDATACOPY;CODECOPY;RETURNDATACOPY;EXTCODECOPY]`
  >- suspend "copy" >>
  Cases_on `i.inst_opcode = SHA3` >- suspend "sha3" >>
  Cases_on `i.inst_opcode = LOG` >- suspend "log" >>
  Cases_on `MEM i.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]`
  >- suspend "guard" >>
  Cases_on `i.inst_opcode = INITIAL_FMP` >- suspend "fmp" >>
  Cases_on `i.inst_opcode = GAS` >- suspend "gas" >>
  Cases_on `MEM i.inst_opcode [BYTE;SIGNEXTEND]` >- suspend "byte" >>
  Cases_on `MEM i.inst_opcode
    [CALLER;ADDRESS;CALLVALUE;ORIGIN;GASPRICE;CHAINID;COINBASE;TIMESTAMP;
     NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;BLOCKHASH;BLOBHASH;
     CALLDATASIZE;CALLDATALOAD;RETURNDATASIZE;CODESIZE]`
  >- suspend "environment" >>
  Cases_on `i.inst_opcode = BUMP` >- suspend "bump" >>
  Cases_on `MEM i.inst_opcode [SLOAD;TLOAD]` >- suspend "storage_read" >>
  Cases_on `MEM i.inst_opcode [BALANCE;SELFBALANCE;EXTCODESIZE;EXTCODEHASH]`
  >- suspend "account" >>
  Cases_on `MEM i.inst_opcode [SSTORE;TSTORE]` >- suspend "storage_write" >>
  `i.inst_opcode = OFFSET` by (fs[MEM] >> metis_tac[]) >>
  drule_all ld_normal_offset_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[scalar]:
  `?out. i.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     qpat_x_assum `MEM i.inst_opcode [MUL;Div;Mod;SDIV;SMOD;Exp;ADDMOD;MULMOD;SLT;SGT;ISZERO;AND;OR;XOR;NOT]` mp_tac >>
     simp[MEM] >> strip_tac >> simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all ld_normal_clean_scalar_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[assign]:
  `?op out. i.inst_operands = [op] /\ i.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all ld_normal_assign_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[param]:
  `?idx out. i.inst_operands = [Lit idx] /\ i.inst_outputs = [out]` by
    (irule ld_normal_parameter_shape >> simp[] >> fs[MEM]) >>
  qpat_x_assum `MEM i.inst_opcode [PARAM;RETPC_PARAM]` mp_tac >>
  simp[MEM] >> strip_tac
  >- (drule_all ld_normal_param_backward >> simp[]) >>
  drule_all ld_normal_retpc_param_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[affine]:
  `i.inst_opcode = ADD \/ i.inst_opcode = SUB` by fs[MEM] >>
  `?a b out. i.inst_operands = [a;b] /\ i.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  metis_tac[ld_normal_affine_backward]
QED

Resume ld_normal_ordinary_backward[shift]:
  `?n v out. i.inst_operands = [n;v] /\ i.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     qpat_x_assum `MEM i.inst_opcode [SHL;SHR;SAR]` mp_tac >>
     simp[MEM] >> strip_tac >> simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all ld_normal_shift_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[compare]:
  `?a b out. i.inst_operands = [a;b] /\ i.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     qpat_x_assum `MEM i.inst_opcode [EQ;LT;GT]` mp_tac >>
     simp[MEM] >> strip_tac >> simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all ld_normal_compare_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[mload]:
  `?op out. i.inst_operands = [op] /\ i.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all ld_normal_mload_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[iload]:
  `?op out. i.inst_operands = [op] /\ i.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all ld_normal_iload_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[mstore]:
  `?a b. i.inst_operands = [a;b] /\ i.inst_outputs = []` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all ld_normal_mstore_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[mstore8]:
  `?a b. i.inst_operands = [a;b] /\ i.inst_outputs = []` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all ld_normal_mstore8_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[istore]:
  `?a b. i.inst_operands = [a;b] /\ i.inst_outputs = []` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all ld_normal_istore_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[mcopy]:
  `?a b c. i.inst_operands = [a;b;c] /\ i.inst_outputs = []` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all ld_normal_mcopy_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[copy]:
  `?addr dst off sz.
     i.inst_operands = (if i.inst_opcode = EXTCODECOPY then [addr;dst;off;sz]
                       else [dst;off;sz]) /\ i.inst_outputs = []` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     qpat_x_assum `MEM i.inst_opcode [CALLDATACOPY;CODECOPY;RETURNDATACOPY;EXTCODECOPY]` mp_tac >>
     simp[MEM] >> strip_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all ld_normal_payload_copy_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[sha3]:
  `?off sz. i.inst_operands = [off;sz]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all ld_normal_sha3_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[log]:
  `?tc off sz topics.
     i.inst_operands = Lit tc :: REVERSE (off::sz::topics) /\
     LENGTH topics = w2n tc /\ i.inst_outputs = []` by
    (drule_all ld_normal_log_shape >> simp[]) >>
  drule_all ld_normal_log_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[guard]:
  drule_all ld_normal_guard_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[fmp]:
  drule_all ld_normal_initial_fmp_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[gas]:
  drule_all ld_normal_gas_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[byte]:
  drule_all ld_normal_byte_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[environment]:
  drule_all ld_normal_environment_read_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[bump]:
  drule_all ld_normal_bump_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[storage_read]:
  drule_all ld_normal_storage_read_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[account]:
  drule_all ld_normal_account_read_backward >> simp[]
QED

Resume ld_normal_ordinary_backward[storage_write]:
  drule_all ld_normal_storage_write_backward >> simp[]
QED

Finalise ld_normal_ordinary_backward

(* PREMISE-TO-SOURCE TABLE for the exported dispatcher.
All wrappers return the displayed single source witness and the SAME entire
normal-data successor.  No existential witnesses need to be joined.
Common environmental, support, normal-mode and comparison premises above are
retained, not inferred from normal_data.  inst_wf i follows from
ld_annotated_inst_wf (shape + fn_ptr_ok + annotated reachability).

ld_normal_clean_scalar_backward:
  [MUL;Div;Mod;SDIV;SMOD;Exp;ADDMOD;MULMOD;SLT;SGT;ISZERO;AND;OR;XOR;NOT].
  singleton outputs: inst_wf_def + LENGTH_EQ_NUM_compute.
ld_normal_assign_backward: ASSIGN, singleton operands/output: same rewrites.
ld_normal_param_backward / ld_normal_retpc_param_backward:
  PARAM / RETPC_PARAM, literal singleton shape: ld_normal_parameter_shape.
  PARAM's envelope includes the root-entry alternative; NO AP-length premise.
ld_normal_affine_backward: ADD/SUB, two operands/one output: wf rewrites.
ld_normal_shift_backward: SHL/SHR/SAR, two operands/one output: wf rewrites.
ld_normal_compare_backward: EQ/LT/GT, two operands/one output: wf rewrites.
  Its extra headroom, stack-origin and suspended-cardinality premises are
  explicit in the candidate, not alleged consequences of annotated_reachable.
ld_normal_mload_backward / ld_normal_iload_backward: MLOAD/ILOAD,
  singleton operands/output: wf rewrites; normal-mode exclusion explicit.
ld_normal_mstore_backward / ld_normal_mstore8_backward /
ld_normal_istore_backward: MSTORE/MSTORE8/ISTORE,
  two operands/no outputs: wf rewrites; normal-mode exclusion explicit.
ld_normal_mcopy_backward: MCOPY, three operands/no outputs: wf rewrites.
ld_normal_payload_copy_backward:
  CALLDATACOPY/CODECOPY/RETURNDATACOPY: three operands/no outputs;
  EXTCODECOPY: four operands/no outputs; wf rewrites after opcode split.
ld_normal_sha3_backward: SHA3, two operands: wf rewrites.
ld_normal_log_backward: LOG, reversed tail and no outputs: ld_normal_log_shape.
  Topic definedness/count and static checks are derived inside the wrapper
  from target success; they are NOT extra dispatcher assumptions.
ld_normal_guard_backward: NOP/ASSERT/ASSERT_UNREACHABLE, no extra shapes.
ld_normal_initial_fmp_backward: INITIAL_FMP, no extra shapes/support.
ld_normal_gas_backward: GAS, no extra shapes/support.
ld_normal_byte_backward: BYTE/SIGNEXTEND, no extra shapes.
ld_normal_environment_read_backward:
  CALLER/ADDRESS/CALLVALUE/ORIGIN/GASPRICE/CHAINID/COINBASE/TIMESTAMP/NUMBER/
  PREVRANDAO/GASLIMIT/BASEFEE/BLOBBASEFEE/BLOCKHASH/BLOBHASH/CALLDATASIZE/
  CALLDATALOAD/RETURNDATASIZE/CODESIZE, no extra shapes.
ld_normal_bump_backward: BUMP, no extra shapes.
ld_normal_storage_read_backward: SLOAD/TLOAD, no extra shapes.
ld_normal_account_read_backward: BALANCE/SELFBALANCE/EXTCODESIZE/EXTCODEHASH,
  no extra shapes.
ld_normal_storage_write_backward: SSTORE/TSTORE, inst_wf from annotated shape.

COMPLEMENT / OWNER MAP
MEMTOP/DRET/GETFMP/SETFMP/RETFMP/FMP_PARAM: impossible by fn_ptr_ok_def
at a member instruction.  FMP_PARAM shape above does not make it a wrapper.
JMP/JNZ/DJMP/PHI: C2.control (PHI uses parallel entered-block semantics).
RET: C2.calls; INVOKE: C2.calls.
RETURN/REVERT/STOP/SINK/INVALID: C2.terminal (some cannot return OK).
CALL/STATICCALL/DELEGATECALL/CREATE/CREATE2/SELFDESTRUCT: C2.external,
with terminal handling where appropriate.
ALLOCA/DALLOCA/DLOAD/DLOADBYTES: C2.allocation and macro modes.
OFFSET: the gap found by this audit is now filled by the separate
  ld_normal_offset_backward producer. Its premises are annotated reachability,
  context shape, fn_ptr_ok for members, normal_data, opcode and target OK;
  all are present in the candidate. Literal/label shape follows from inst_wf;
  no variable support, pointer, opaque-use or normal-mode premise is needed.
  The producer checks clean output provenance/taint and retains all companions.
  This resolves the finite family gap, NOT recursive temporal coverage.
*)
