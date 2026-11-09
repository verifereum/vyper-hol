Theory loadElimStoreEquivalence
Ancestors
  loadElimKeyRead dfgCorrectnessProof dfgDefs venomState venomInst list

(* The store test normalizes only pairs of variables. *)
Theorem le_store_equiv_eval:
  dfg_assigns_sound d s /\
  (case (a,b) of
     (Var _, Var _) => normalize_operand d [] a = normalize_operand d [] b
   | _ => a = b) ==>
  eval_operand a s = eval_operand b s
Proof
  Cases_on `a` >> Cases_on `b` >> simp[] >> strip_tac >>
  metis_tac[normalize_operand_eval_proof]
QED

Theorem le_store_equiv_list_read:
  dfg_assigns_sound d s /\
  EVERY (\a. case (a,value) of
     (Var _, Var _) => normalize_operand d [] a = normalize_operand d [] value
   | _ => a = value) vs /\
  MEM op vs /\ le_key_read space key s = eval_operand op s ==>
  le_key_read space key s = eval_operand value s
Proof
  strip_tac >>
  `eval_operand op s = eval_operand value s` by
    (irule le_store_equiv_eval >> qexists `d` >>
     gvs[EVERY_MEM]) >>
  simp[]
QED
