(* A typed offset into inactive capacity does not identify a live selection.
   This refutes an endpoint-only route, not intcall_arg_provenance_held. *)
Theory bodyIntCallPostProvenanceEndpointProbe
Ancestors
  bodyIntCallPathLayout loweringPosts valueEncoding valueEncodingDefs words

Theorem inactive_dynamic_path_endpoint:
  value_has_type (ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1))
    (ArrayV (DynArrayV [])) /\
  mem_path_offset (ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1))
    [ValueSubscript (IntV 0)] =
      SOME (32, ArrayTV (BaseTV BoolT) (Dynamic 1)) /\
  val_in_memory (ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1))
    (ArrayV (DynArrayV [])) 0 [] /\
  val_in_memory (ArrayTV (BaseTV BoolT) (Dynamic 1))
    (ArrayV (DynArrayV [])) 32 [] /\
  val_wf (ArrayTV (BaseTV BoolT) (Dynamic 1)) (ArrayV (DynArrayV [])) /\
  value_has_type (ArrayTV (BaseTV BoolT) (Dynamic 1))
    (ArrayV (DynArrayV [])) /\
  ~sub_layout (ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1))
    (ArrayV (DynArrayV [])) 32 (ArrayTV (BaseTV BoolT) (Dynamic 1))
    (ArrayV (DynArrayV []))
Proof
  simp_tac (srw_ss()) [LET_THM] >>
  rpt conj_tac
  >~ [`~sub_layout _ _ _ _ _`]
  >- (simp[sub_layout_def, type_memory_size_def] >>
      qexistsl [`0`, `REPLICATE 63 (0w:byte) ++ [1w]`] >> EVAL_TAC >> simp[]) >>
  EVAL_TAC >> simp[]
QED
