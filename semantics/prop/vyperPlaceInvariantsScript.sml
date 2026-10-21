Theory vyperPlaceInvariants
Ancestors
  list finite_map vyperState vyperTyping vyperTypeInvariants

(* Historical values are typed at their resolved, root-first paths, not at
   the current dynamic lengths. This invariant is additive to state typing. *)
Definition popped_history_typed_def:
  popped_history_typed tv history <=>
    !path v. MEM (path,v) history ==>
      ?ptv. subscripts_type tv path = SOME ptv /\
            well_formed_type_value ptv /\ value_has_type ptv v
End

Definition scope_history_typed_def:
  scope_history_typed sc <=>
    !id entry. FLOOKUP sc id = SOME entry ==>
      popped_history_typed entry.type entry.popped
End

Definition state_history_typed_def:
  state_history_typed st <=> EVERY scope_history_typed st.scopes
End

Definition place_state_well_typed_def:
  place_state_well_typed st <=>
    state_well_typed st /\ state_history_typed st
End

Theorem popped_history_typed_nil[simp]:
  popped_history_typed tv []
Proof
  simp[popped_history_typed_def]
QED

Theorem popped_history_typed_cons:
  popped_history_typed tv ((path,v)::history) <=>
    (?ptv. subscripts_type tv path = SOME ptv /\
           well_formed_type_value ptv /\ value_has_type ptv v) /\
    popped_history_typed tv history
Proof
  simp[popped_history_typed_def] >> metis_tac[]
QED

Theorem lookup_scopes_history_typed:
  !scopes id entry. EVERY scope_history_typed scopes /\
    lookup_scopes id scopes = SOME entry ==>
    popped_history_typed entry.type entry.popped
Proof
  Induct >> simp[lookup_scopes_def] >> rpt gen_tac >>
  Cases_on `FLOOKUP h id` >> simp[] >>
  metis_tac[scope_history_typed_def]
QED

Theorem state_history_typed_lookup:
  state_history_typed st /\ lookup_scopes id st.scopes = SOME entry ==>
    popped_history_typed entry.type entry.popped
Proof
  simp[state_history_typed_def] >> metis_tac[lookup_scopes_history_typed]
QED

Theorem scope_history_typed_empty[simp]:
  scope_history_typed FEMPTY
Proof
  simp[scope_history_typed_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles andalso null axioms
     then print ("Kernel-closed place invariant: " ^ name ^ "\n")
     else raise Fail ("Incomplete place invariant: " ^ name)
  end) (DB.thms "vyperPlaceInvariants");
