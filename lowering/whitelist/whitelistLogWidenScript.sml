(* Log arguments may have smaller scalar bounds than their declared fields.
   Argument evaluation and the ABI buffer use the saved physical layouts.
   The separate declared non-indexed layout bound ensures those source
   field types evaluate. Scalar compatibility preserves topic encoding,
   ABI encoding and each value's occupied memory footprint.
   An indexed declared StringT (2 ** 256), paired with a StringT 1 argument,
   can satisfy the helper premises while the declared type does not evaluate.
   Indexed hashing ignores that capacity. The helpers therefore do not imply
   that every declared indexed field has an evaluated type. *)
Theory whitelistLogWiden
Ancestors
  allocLimits allocLimitsProps eventEncodingProps eventLoweringStructure
  valueCopyBytes valueTypingMemoryProps vyperEventCompatibility
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  stmtSimLogArgsRun stmtSimLogArgsGrowth stmtSimLogSuffix stmtSimLogSource
  exprSimWordArgs stmtSimLogSuffixFrame
  stmtSimLogSuffixCode stmtSimLogArgs freshWrites logComposeFacts
  compileEnv loweringStateRelDefs stmtLowering fragExec loweringSlice exprLoweringProps
  emitHelperProps vyperInterpreter vyperState vyperTyping list
  stmtSimLogTrace emitHelper context venomInst
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasMode fragGasPath fragGasSeq rich_list fragGasSeqAbort
  stmtSimLogCompose stmtSimLog bodySimLogArgs e2eDefs vyperEvent vyperEventArgCompat vyperABI
  vyperEventSoundness vyperTypeSystem supportedTypes supportedDecls supportedStmts
  supportedExprs supportedExprTraverse supportedStmtTraverse
  exprSimSource bodyExprPreFacts exprSimHypsDefs bodySim exprSimHyps
  compileVyper vyperTypeInvariants supportedProgram supportedNames vyperContext
  vyperTypeExprSoundness vyperTypeCallGraph vyperTypeCallStackSoundness
Libs
  monadsyntax logWidenTacticsLib

(* ===== The source encoding ignores a bytestring argument's bound ===== *)

Theorem event_arg_compatible_cases[local]:
  (!fty aty. event_arg_compatible fty aty ==>
     aty = fty \/
     (?n m. fty = BaseT (StringT n) /\ aty = BaseT (StringT m)) \/
     (?n m. fty = BaseT (BytesT (Dynamic n)) /\
            aty = BaseT (BytesT (Dynamic m))) \/
     (?t b. fty = ArrayT t b) \/ (?ts. fty = TupleT ts)) /\
  (!fs ats. event_arg_compatible_list fs ats ==> T)
Proof
  logWidenTacticsLib.compatible_cases
QED

Theorem event_leaf_arg_compatible:
  !fty aty tenv.
    supported_event_leaf_type fty /\ event_arg_compatible fty aty ==>
    supported_event_leaf_type aty /\
    vyper_to_abi_type tenv aty = vyper_to_abi_type tenv fty /\
    (!v. vyper_to_abi tenv aty v = vyper_to_abi tenv fty v) /\
    (!v. encode_event_topic aty v = encode_event_topic fty v)
Proof
  rpt gen_tac >> strip_tac >>
  drule (CONJUNCT1 event_arg_compatible_cases) >> strip_tac >>
  gvs[supported_event_leaf_type_def, supported_scalar_type_def,
      supported_word_type_def, supported_string_type_def] >>
  rw[supported_event_leaf_type_def, supported_scalar_type_def,
     supported_word_type_def, supported_string_type_def, encode_event_topic_def,
     is_event_bytestring_type_def] >>
  Cases_on `v` >> simp[]
QED

Theorem scalar_event_arg_compatible:
  !fty aty tenv.
    supported_scalar_type fty /\ event_arg_compatible fty aty ==>
    supported_scalar_type aty /\
    vyper_to_abi_type tenv aty = vyper_to_abi_type tenv fty /\
    (!v. vyper_to_abi tenv aty v = vyper_to_abi tenv fty v) /\
    (!v. encode_event_topic aty v = encode_event_topic fty v)
Proof
  rpt gen_tac >> strip_tac >>
  `supported_event_leaf_type fty` by simp[supported_event_leaf_type_def] >>
  drule_all event_leaf_arg_compatible >> strip_tac >> simp[] >>
  drule (CONJUNCT1 event_arg_compatible_cases) >> strip_tac >>
  gvs[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def]
QED

Theorem event_leaf_compatible_topics_eq:
  !tys atys flags vals.
    EVERY supported_event_leaf_type tys /\ LIST_REL event_arg_compatible tys atys ==>
    encode_indexed_event_topics flags atys vals =
    encode_indexed_event_topics flags tys vals
Proof
  logWidenTacticsLib.topics_eq event_leaf_arg_compatible
QED

Theorem compatible_non_indexed:
  !flags tys atys.
    EVERY P tys /\ LIST_REL event_arg_compatible tys atys ==>
    EVERY P (log_non_indexed_types flags tys) /\
    LIST_REL event_arg_compatible (log_non_indexed_types flags tys)
      (log_non_indexed_types flags atys)
Proof
  rpt strip_tac >>
  mp_tac (Q.INST [`R` |-> `event_arg_compatible`, `Q` |-> `K T`,
                  `ftys` |-> `tys`] log_non_indexed_types_preserve) >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem event_leaf_compatible_abi_eq:
  !tys atys vals.
    EVERY supported_event_leaf_type tys /\ LIST_REL event_arg_compatible tys atys ==>
    vyper_to_abi_types tenv atys = vyper_to_abi_types tenv tys /\
    vyper_to_abi_list tenv atys vals = vyper_to_abi_list tenv tys vals
Proof
  logWidenTacticsLib.abi_eq event_leaf_arg_compatible
QED

(* log_source_event_encoded with the metadata at the field types tys and
   the values typed at compatible argument types atys. *)
Theorem log_source_event_encoded_widen:
  lookup_event_metadata tenv sources target id = SOME (h, tys, flags) /\
  EVERY supported_event_leaf_type tys /\
  LIST_REL event_arg_compatible tys atys /\
  LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\
                            value_has_type tv v) atys vals /\
  LENGTH flags = LENGTH tys ==>
  ?topics avs.
    encode_indexed_event_topics flags atys vals = SOME topics /\
    vyper_to_abi_list tenv (log_non_indexed_types flags atys)
      (log_non_indexed_values flags vals) = SOME avs /\
    encode_source_event tenv sources target id vals =
      SOME <| logger := target; topics := n2w h :: topics;
              data := enc (Tuple (vyper_to_abi_types tenv
                                  (log_non_indexed_types flags atys)))
                          (ListV avs) |>
Proof
  strip_tac >>
  `EVERY supported_event_leaf_type atys` by
    (gvs[EVERY_EL, LIST_REL_EL_EQN] >>
     metis_tac[event_leaf_arg_compatible]) >>
  `LENGTH atys = LENGTH tys /\ LENGTH vals = LENGTH atys` by
    metis_tac[LIST_REL_LENGTH] >>
  `LENGTH flags = LENGTH atys /\ LENGTH flags = LENGTH vals` by simp[] >>
  drule_all typed_event_args_total >> strip_tac >>
  `?vs. non_indexed_event_args flags atys vals = SOME vs /\
        MAP FST vs = log_non_indexed_types flags atys /\
        MAP SND vs = log_non_indexed_values flags vals` by
    metis_tac[non_indexed_event_args_exists] >>
  gvs[] >>
  qspecl_then [`flags`, `tys`, `atys`] mp_tac
    (Q.INST [`P` |-> `supported_event_leaf_type`] compatible_non_indexed) >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`log_non_indexed_types flags tys`,
               `log_non_indexed_types flags atys`,
               `log_non_indexed_values flags vals`] mp_tac event_leaf_compatible_abi_eq >>
  impl_tac >- simp[] >> strip_tac >>
  `encode_indexed_event_topics flags tys vals = SOME topics` by
    metis_tac[event_leaf_compatible_topics_eq] >>
  `?vs. non_indexed_event_args flags tys vals = SOME vs /\
        MAP FST vs = log_non_indexed_types flags tys /\
        MAP SND vs = log_non_indexed_values flags vals` by
    metis_tac[non_indexed_event_args_exists] >>
  gvs[encode_source_event_def, encode_vyper_event_metadata_def]
QED

(* ===== Statement simulation ===== *)
