# Exact TASK target inventory (2026-11-04)

This is partial-completion accounting, not certification of the TASK.
All names in the table have the suffix `Theory` (omitted for readability).
B = dependency-blocked, P = independent pending verification, S = whole-target build evidence.
No B entry is a falsehood claim. No passing prefix is counted as S.

## Dependency path dictionary

Each path is a sequence of source Ancestors edges, ending at unresolved
`exprSimUnwrap.unwrap_copy_sim`. U = exprSimUnwrap itself.
H = exprSimHyps -> U.
C = exprSimConvert -> H.
D = entryDecodeProps -> C.
A = abiDecodeStaticProps -> D.
E = entryDecodeStaticProps -> D.
L = exprSimLeaves -> U.
R = stmtSimReturn -> L.
V = valueCopy -> D.
G = exprSimAggregateChildren -> H.
T = ctorAbiActualArrayBody -> entryDecodeStructure -> D.
F = ctorAbiActualArrayFinite -> ctorAbiActualArrayBody -> T (omit duplicate node).
N = ctorAbiActualArrayEntry -> F.
X = ctorAbiActualArrayContext -> N.
Y = ctorAbiActualArrayRun -> X.
Z = ctorAbiActualArrayClosure -> Y.
Q = ctorAbiActualRecursive -> Z.
For a table row `B: H`, prepend the row name to H unless identical.

Source evidence: tool outputs m0336 (expr imports), m0337 (entry imports),
m0346 (stmt), m0347 (body), m0348/m0353-m0355 (ctor), m0350 (intCall),
m0351 (valueCopy), m0352 (tuple), m0356 (abiDecodeStaticProps),
m0357-m0361/m0364 (remaining imports), all under
TO_seq1012_cone-20261104T041205Z_.

The independent queue uses established built prerequisites from E0006/E0010/E0011
and source Ancestors closure. In particular core expression/operand theories
are prerequisites of Unwrap, not its dependents. The independent statement
store/control chain imports stmtSim, exprSim, exprLoweringProps and lower-level
compiler/semantic theories; it does not import Hyps/Unwrap. exprWordOperand's
closure is exprSafeOperand/Builtins and compiler/typing theories (m0336).
No unresolved/nonliteral dependency is assumed independent.

## Exact target table

| Target | Status / prerequisite path |
|---|---|
| abiDecodeStaticProps | B: D |
| bodyMemoryDefs | B: H |
| bodySim | B: H |
| bodySimEntry | B: bodySim -> H |
| bodySimExprCases | B: H; tuple-base exception also downstream |
| ctorAbiActual | B: Q |
| ctorAbiActualArrayBody | B: T |
| ctorAbiActualArrayClosure | B: Z |
| ctorAbiActualArrayContext | B: X |
| ctorAbiActualArrayEntry | B: N |
| ctorAbiActualArrayFinite | B: F |
| ctorAbiActualArrayHeader | B: ctorAbiActualArrayBody -> T |
| ctorAbiActualArrayRun | B: Y |
| ctorAbiActualRecursive | B: Q |
| entryArgPtrs | B: D |
| entryChecksProps | B: D |
| entryDecodePlanProps | B: D |
| entryDecodeProps | B: D |
| entryDecodeStaticProps | B: E |
| entryDecodeStructure | B: D |
| entryHaltMem | B: D |
| entrySinkExtraction | B: A |
| entryStateRel | B: entryDecodePlanProps -> D |
| exprOpenCases | B: H |
| exprOpenCopies | B: H |
| exprOpenDispatch | B: exprOpenCases -> H |
| exprOpenFirstOperand | B: H |
| exprOpenMain | B: H |
| exprOperandVar | S |
| exprReasonOperand | B: stmtSimReasonExpr -> U |
| exprSafeOperand | S |
| exprSafeOperandBuiltins | S |
| exprSim | S |
| exprSimAccounts | B: H |
| exprSimAggregateChildren | B: G |
| exprSimAggregateLayout | B: H |
| exprSimAggregateLoops | B: H |
| exprSimAggregateSource | B: H |
| exprSimAggregates | B: H |
| exprSimArith | S |
| exprSimArrayIndex | S |
| exprSimAttribute | B: H |
| exprSimAttributeFields | B: H |
| exprSimBinopFrag | B: H |
| exprSimBuffer | B: exprSimWordArgs -> H |
| exprSimBufferEmptyExec | B: exprSimBuffer -> exprSimWordArgs -> H |
| exprSimBufferStore | B: D |
| exprSimBuiltins | B: H |
| exprSimCalldata | B: H |
| exprSimCalldataSlice | B: H |
| exprSimCalls | B: H |
| exprSimCompare | S |
| exprSimConvert | B: C |
| exprSimCopy | S |
| exprSimECArith | B: H |
| exprSimHash | B: H |
| exprSimHyps | B: H |
| exprSimIfExp | B: U |
| exprSimLeaves | B: L |
| exprSimLen | B: H |
| exprSimLiteralBuffer | B: H |
| exprSimMain | B: H |
| exprSimMemoryTransport | S |
| exprSimOperands | S |
| exprSimOperators | B: H |
| exprSimOps | S |
| exprSimPlaces | B: H; known tuple-base annotation/layout exception |
| exprSimPop | B: H |
| exprSimPrecompiles | B: H |
| exprSimSend | B: H |
| exprSimStorageCopy | S |
| exprSimTuple | B: H; tuple-base users remain uncertified |
| exprSimUnop | S |
| exprSimUnwrap | B: U (unchanged frozen unwrap_copy_sim unresolved) |
| exprSimWordArgs | B: H |
| exprSimWordBuiltins | B: H |
| exprWordOperand | S |
| freshWrites | S |
| intCallArgs | B: V |
| intCallResult | B: D |
| intCallReturn | B: R |
| intCallReturnMem | B: R |
| stmtPoppedKeys | B: H |
| stmtSim | S |
| stmtSimAssign | S |
| stmtSimAssignStore | S |
| stmtSimAugAssign | B: H |
| stmtSimDecl | S |
| stmtSimDeclStore | S |
| stmtSimFor | S |
| stmtSimForLoop | S |
| stmtSimForParts | S |
| stmtSimForRange | S |
| stmtSimIf | S |
| stmtSimLog | S (baseline cheat retained) |
| stmtSimReason | S |
| stmtSimReasonCode | B: U |
| stmtSimReasonExpr | B: U |
| stmtSimReasonStorage | B: U |
| stmtSimReturn | B: R |
| storageCopyLive | B: exprSimAttributeFields -> H |
| targetPlaceSim | B: H |
| targetPlaceSimCases | B: H |
| tupleLoadProps | B: R |
| tupleMemoryFrame | B: G |
| tupleMemoryLayout | S |
| valueCopy | B: V |
| valueCopyBytes | S |
| valueCopySource | B: V |

## Deterministic independent residual queue

Prerequisite-first batches, preserving TASK order among independent peers:

1. exprSimTheory freshWritesTheory exprSimOpsTheory exprSafeOperandTheory exprSafeOperandBuiltinsTheory exprOperandVarTheory exprWordOperandTheory exprSimStorageCopyTheory exprSimCompareTheory exprSimArithTheory exprSimArrayIndexTheory exprSimUnopTheory exprSimMemoryTransportTheory valueCopyBytesTheory exprSimCopyTheory exprSimOperandsTheory
2. stmtSimTheory stmtSimDeclStoreTheory stmtSimIfTheory stmtSimForPartsTheory stmtSimLogTheory tupleMemoryLayoutTheory
3. stmtSimDeclTheory stmtSimAssignStoreTheory stmtSimAssignTheory stmtSimForLoopTheory stmtSimForTheory stmtSimForRangeTheory stmtSimReasonTheory

No B target may be submitted to holbuild while U remains unresolved.
Filtered validation completed: batch 1 passed in tool output
TO_seq1012_cone-20261104T041205Z_m0366_t001; batch 2 in m0367_t001;
batch 3 in m0368_t001 (same prefix). All 29 queued whole targets pass.
The independent residual queue is now empty. Builds retained proof steps,
default timeout, no flags. No proof source was edited in this inventory.

## Final partial accounting

Every exact TASK target is listed above. S entries are whole-target success,
not merely successful prefixes. All remaining B entries have an explicit
source-import path to the unchanged unresolved unwrap_copy_sim. They have not
been certified and have not been admitted. No new independent failure was
exposed. Known tuple-base unsupported consumers remain separately noted;
this inventory does not assert they are false or repaired. The approved-helper
ledger is L0003, and the unresolved Unwrap audit/skip record is L0006/E0017.

The TASK completion criteria are NOT met: the full target list cannot pass
with unresolved Unwrap. No full-build or no-oracle-tag certification is claimed.
The passing uncommitted Unwrap prefix edits remain intact, unchanged here,
and must not be confused with whole-theory success.
