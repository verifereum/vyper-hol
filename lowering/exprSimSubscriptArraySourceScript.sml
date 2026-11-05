(* Source read boundaries for framed array subscript simulation. *)
Theory exprSimSubscriptArraySource
Ancestors
  exprSimSource vyperState vyperInterpreter vyperValue integer option list

Theorem read_result_nonstorage_frame:
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  s'.scopes = s.scopes /\ s'.immutables = s.immutables ==>
  FST (read_result cx r s') = FST (read_result cx r s)
Proof
  strip_tac >> Cases_on `r`
  >- simp[read_result_def, return_def]
  >- (Cases_on `p`
      >- metis_tac[]
      >- (rename1 `PlaceR (MemoryPlace id path)` >>
          simp[read_result_def, read_place_def, get_scopes_def, bind_def,
               lift_option_type_def, lift_sum_def, return_def, raise_def] >>
          Cases_on `lookup_scopes id s.scopes` >>
          simp[return_def, raise_def] >>
          rename1 `lookup_scopes id s.scopes = SOME entry` >>
          Cases_on `read_memory_path entry path` >> simp[return_def, raise_def])
      >> simp[read_result_def, read_place_def, get_immutables_def,
              get_address_immutables_def, bind_def, lift_option_type_def,
              lift_sum_def, return_def, raise_def] >>
      rpt (CASE_TAC >> simp[return_def, raise_def, bind_def]))
  >> simp[read_result_def, raise_def]
QED

(* A stale child snapshot refutes an unrestricted read/selection equation.
   This history is typed, but its child key is not indexed through a dynamic
   array, as expr_sim_inv requires. *)
Theorem fixed_array_snapshot_probe[local]:
  let tv = ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (Dynamic 2);
      p = [ValueSubscript (IntV 0)];
      hist = [(p ++ [ValueSubscript (IntV 0)], IntV 9);
              (p, ArrayV (StaticArrayV [IntV 5; IntV 1]))]
  in read_popped tv p hist = SOME (ArrayV (StaticArrayV [IntV 5; IntV 1])) /\
     read_popped tv (p ++ [ValueSubscript (IntV 0)]) hist = SOME (IntV 9)
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED
