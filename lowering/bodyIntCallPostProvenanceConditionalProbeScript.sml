(* The conditional expression retains views of aggregate memory values. *)
Theory bodyIntCallPostProvenanceConditionalProbe
Ancestors
  vyperState

Theorem conditional_result_memory_aggregate:
  place_type_value cx (MemoryPlace n path) es = (INL tv,ee) /\
  ((?et bd. tv = ArrayTV et bd) \/ (?ts. tv = TupleTV ts) \/
   (?fs. tv = StructTV fs) \/
   (?m. tv = BaseTV (BytesT (Dynamic m))) \/
   (?m. tv = BaseTV (StringT m))) ==>
  conditional_result cx (PlaceR (MemoryPlace n path)) es =
    (INL (PlaceR (MemoryPlace n path)),ee)
Proof
  strip_tac >>
  simp[conditional_result_def, bind_def, return_def]
QED
