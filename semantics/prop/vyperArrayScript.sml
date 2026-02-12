Theory vyperArray

Ancestors
  vyperInterpreter

Definition array_is_mutable_def[simp]:
  array_is_mutable (DynArrayV _ _ _) = T ∧
  array_is_mutable (SArrayV _ _ _) = T ∧
  array_is_mutable (TupleV _) = F
End

Definition array_is_dynamic_def[simp]:
  array_is_dynamic (DynArrayV _ _ _) = T ∧
  array_is_dynamic (SArrayV _ _ _) = F ∧
  array_is_dynamic (TupleV _) = F
End

Definition valid_index_def[simp]:
  valid_index a (i:int) ⇔ 0 ≤ i ∧ i < &array_length a
End

Theorem array_index_valid:
  ∀a i. valid_index a i ⇔ IS_SOME (array_index a i)
Proof
  cheat
QED

Theorem array_set_index_valid:
  ∀a i v. array_is_mutable a ∧ valid_index a i ⇔ ∃a'. array_set_index a i v = INL (ArrayV a')
Proof
  cheat
QED

Theorem array_length_after_set:
  ∀a a' i v. array_set_index a i v = INL (ArrayV a') ⇒ array_length a' = array_length a
Proof
  cheat
QED

Theorem array_index_after_set_same:
  ∀a a' i v. array_set_index a i v = INL (ArrayV a') ⇒ array_index a' i = SOME v
Proof
  cheat
QED

Theorem array_index_after_set_other:
  ∀a a' i j v. i ≠ j ∧ array_set_index a i v = INL (ArrayV a') ⇒ array_index a' j = array_index a j
Proof
  cheat
QED

Theorem array_length_after_pop:
  ∀a a'. pop_element (ArrayV a) = INL (ArrayV a') ⇒ array_length a' = array_length a - 1
Proof
  cheat
QED

Theorem array_index_after_pop:
  ∀a a' i. valid_index a' i ∧ pop_element (ArrayV a) = INL (ArrayV a') ⇒ array_index a i = array_index a' i
Proof
  cheat
QED

Theorem array_pop_valid:
  ∀a. array_is_dynamic a ∧ array_length a ≠ 0 ⇔ ∃a'. pop_element (ArrayV a) = INL (ArrayV a')
Proof
  cheat
QED

Theorem array_length_after_append:
  ∀a a' v. append_element (ArrayV a) v = INL (ArrayV a') ⇒ array_length a' = array_length a + 1
Proof
  cheat
QED

Theorem array_index_after_append:
  ∀a a' v. append_element (ArrayV a) v = INL (ArrayV a') ⇒ ∃ty v'. safe_cast ty v = SOME v' ∧ array_index a' &(array_length a) = SOME v'
Proof
  cheat
QED

Theorem array_index_after_append_other:
  ∀a a' i v. valid_index a i ∧ append_element (ArrayV a) v = INL (ArrayV a') ⇒ array_index a' i = array_index a i
Proof
  cheat
QED

Theorem array_elements_length:
  ∀a. LENGTH (array_elements a) = array_length a
Proof
  cheat
QED

Theorem array_elements_index:
  ∀a i v. valid_index a i ⇒ (EL (Num i) (array_elements a) = v ⇔ array_index a i = SOME v)
Proof
  cheat
QED

Theorem array_elements_after_set:
  ∀a a' i v.
    array_set_index a i v = INL (ArrayV a') ⇒
    array_elements a' = (TAKE (Num i) (array_elements a) ++ [v] ++ DROP (SUC (Num i)) (array_elements a))
Proof
  cheat
QED

Theorem array_elements_after_pop:
  ∀a a'.
    pop_element (ArrayV a) = INL (ArrayV a') ⇒
    array_elements a' = FRONT (array_elements a)
Proof
  cheat
QED

Theorem array_elements_after_append:
  ∀a a' v.
    append_element (ArrayV a) v = INL (ArrayV a') ⇒
    ∃ty v'. safe_cast ty v = SOME v' ∧ array_elements a' = array_elements a ++ [v']
Proof
  cheat
QED
