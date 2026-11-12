(* A typed offset into inactive capacity does not identify a live selection.
   This refutes an endpoint-only route, not intcall_arg_provenance_held. *)
Theory bodyIntCallPostProvenanceEndpointProbe
Ancestors
  bodyIntCallPathLayout loweringPosts valueEncoding valueEncodingDefs words

Theorem inactive_dynamic_path_endpoint:
  let inner = ArrayTV (BaseTV BoolT) (Dynamic 1);
      outer = ArrayTV inner (Dynamic 1);
      empty = ArrayV (DynArrayV [])
  in
    value_has_type outer empty /\
    mem_path_offset outer [ValueSubscript (IntV 0)] = SOME (32,inner) /\
    val_in_memory outer empty 0 [] /\
    val_in_memory inner empty 32 [] /\
    val_wf inner empty /\
    value_has_type inner empty /\
    ~sub_layout outer empty 32 inner empty
Proof
  simp_tac (srw_ss()) [LET_THM] >>
  rpt conj_tac
  >~ [`~sub_layout _ _ _ _ _`]
  >- (simp[sub_layout_def, type_memory_size_def] >>
      qexistsl [`0`, `REPLICATE 63 (0w:byte) ++ [1w]`] >> EVAL_TAC >> simp[]) >>
  EVAL_TAC >> simp[]
QED
