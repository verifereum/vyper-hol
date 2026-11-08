(* Shared semantic facts for indexed heterogeneous copies. *)
Theory typedCopySemanticIndex
Ancestors
  exprSimTuple exprSimAttributeFields vyperTypeABI vyperTypeSystem
  vyperTypeArgFits vyperValue vyperTyping list

Theorem typed_copy_semantic_index:
  OPT_MMAP (evaluate_type tenv) dtys = SOME dtvs /\
  OPT_MMAP (evaluate_type tenv) stys = SOME stvs /\
  LIST_REL (type_widens_to tenv) stys dtys /\
  values_have_types dtvs vs /\ values_have_types stvs vs /\
  tuple_val_wf vs dtvs /\ tuple_val_wf vs stvs /\
  i < LENGTH dtys ==>
  evaluate_type tenv (EL i dtys) = SOME (EL i dtvs) /\
  evaluate_type tenv (EL i stys) = SOME (EL i stvs) /\
  type_widens_to tenv (EL i stys) (EL i dtys) /\
  value_has_type (EL i dtvs) (EL i vs) /\
  value_has_type (EL i stvs) (EL i vs) /\
  val_wf (EL i dtvs) (EL i vs) /\ val_wf (EL i stvs) (EL i vs)
Proof
  strip_tac >>
  `LENGTH stys = LENGTH dtys /\ LENGTH dtvs = LENGTH dtys /\
   LENGTH stvs = LENGTH dtys /\ LENGTH vs = LENGTH dtys` by
    metis_tac[OPT_MMAP_LENGTH, LIST_REL_LENGTH, values_have_types_length] >>
  metis_tac[opt_mmap_el, values_have_types_el, tuple_val_wf_el, LIST_REL_EL_EQN]
QED
