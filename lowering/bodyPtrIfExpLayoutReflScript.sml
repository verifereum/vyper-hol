Theory bodyPtrIfExpLayoutRefl
Ancestors context vyperAST

(* The S1 reflexivity fact is local; export the shared boundary here. *)
Theorem punnable_reflexive:
  (!ty. punnable ce ty ty) /\
  (!tys. punnable_list ce tys tys)
Proof
  ho_match_mp_tac (legacyInduction.mutual_ind_from_ops type_induction) >>
  simp[punnable_def]
QED

Theorem same_memory_layout_reflexive:
  !ce ty. same_memory_layout ce ty ty
Proof
  simp[same_memory_layout_def, punnable_reflexive]
QED
