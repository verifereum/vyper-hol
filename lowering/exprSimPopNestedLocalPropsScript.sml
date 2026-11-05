Theory exprSimPopNestedLocalProps
Ancestors
  loweringPosts vyperState

(* A readable place cannot come from history when fallback is excluded. *)
Theorem read_memory_path_live:
  !entry path v.
    read_memory_path entry path = INL v /\
    (!err. evaluate_subscripts entry.type entry.value path = INR err ==>
           read_popped entry.type path entry.popped = NONE) ==>
    evaluate_subscripts entry.type entry.value path = INL v
Proof
  rpt gen_tac >>
  Cases_on `evaluate_subscripts entry.type entry.value path` >>
  simp[read_memory_path_def] >>
  Cases_on `read_popped entry.type path entry.popped` >> simp[]
QED

Theorem place_readable_memory_live:
  !cx es id path.
    place_readable cx es (PlaceR (MemoryPlace id path)) /\
    (!entry err.
       lookup_scopes id es.scopes = SOME entry /\
       evaluate_subscripts entry.type entry.value path = INR err ==>
       read_popped entry.type path entry.popped = NONE) ==>
    ?entry v. lookup_scopes id es.scopes = SOME entry /\
              evaluate_subscripts entry.type entry.value path = INL v
Proof
  rpt gen_tac >>
  simp[place_readable_def, read_place_def, bind_def, get_scopes_def,
       lift_option_type_def, lift_sum_def, return_def, raise_def] >>
  Cases_on `lookup_scopes id es.scopes` >>
  simp[vyperStateTheory.raise_def, vyperStateTheory.return_def] >>
  rename1 `lookup_scopes id es.scopes = SOME entry` >>
  Cases_on `read_memory_path entry path` >>
  simp[vyperStateTheory.raise_def, vyperStateTheory.return_def] >>
  rpt strip_tac >> drule read_memory_path_live >> simp[]
QED
