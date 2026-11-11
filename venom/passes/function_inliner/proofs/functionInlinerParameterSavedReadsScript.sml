(* Archived call edges preserve exactly the readable projections of suspended
   parents.  The active head's snapshot is deliberately unconstrained. *)
Theory functionInlinerParameterSavedReads
Ancestors
  functionInlinerParameterAncestors functionInlinerActivation
  functionInlinerOperationalCuts venomState venomInst list

Definition inline_parameter_saved_pair_def:
  inline_parameter_saved_pair
    (p:bool list,child:inline_activation,route:inline_route,snap:inline_logical_snapshot)
    (q:bool list,parent:inline_activation,proute:inline_route,psnap:inline_logical_snapshot) <=>
    ?edge. child.ia_parent = SOME edge /\
      edge.ipe_saved.vs_vars = psnap.ils_state.vs_vars /\
      edge.ipe_saved.vs_labels = psnap.ils_state.vs_labels
End

Definition inline_parameter_saved_reads_def:
  (inline_parameter_saved_reads [] <=> T) /\
  (inline_parameter_saved_reads [x] <=> T) /\
  (inline_parameter_saved_reads (x::y::xs) <=>
    inline_parameter_saved_pair x y /\
    inline_parameter_saved_reads (y::xs))
End

Theorem inline_parameter_saved_reads_root:
  inline_parameter_saved_reads [(p,a,route,snap)]
Proof simp[inline_parameter_saved_reads_def]
QED

Theorem inline_parameter_saved_reads_push:
  inline_parameter_saved_reads ((p,pa,proute,psnap)::rest) /\
  inline_original_child C fuel pa.ia_id occurrence call psnap.ils_state r child cr ==>
  inline_parameter_saved_reads
    ((q,child,route,csnap)::(p,pa,proute,psnap)::rest)
Proof
  simp[inline_parameter_saved_reads_def, inline_parameter_saved_pair_def,
       inline_original_child_def] >> metis_tac[]
QED

Theorem inline_parameter_saved_reads_head_replace:
  inline_parameter_saved_reads ((p,a,route,snap)::rest) ==>
  inline_parameter_saved_reads ((q,a,route',snap')::rest)
Proof
  Cases_on `rest` >> simp[inline_parameter_saved_reads_def] >>
  PairCases_on `h` >> simp[inline_parameter_saved_pair_def]
QED

Theorem inline_parameter_saved_reads_pop:
  inline_parameter_saved_reads (x::xs) ==> inline_parameter_saved_reads xs
Proof Cases_on `xs` >> simp[inline_parameter_saved_reads_def]
QED

Theorem inline_parameter_saved_reads_adjacent:
  !prefix child parent rest.
    inline_parameter_saved_reads (prefix ++ child::parent::rest) ==>
    inline_parameter_saved_pair child parent
Proof
  Induct >> simp[inline_parameter_saved_reads_def] >>
  Cases_on `prefix` >> simp[inline_parameter_saved_reads_def] >> metis_tac[APPEND]
QED

Theorem inline_parameter_saved_pair_operand:
  inline_parameter_saved_pair (p,child,route,snap) (q,pa,proute,psnap) /\
  child.ia_parent = SOME edge ==>
  eval_operand op edge.ipe_saved = eval_operand op psnap.ils_state
Proof
  strip_tac >> gvs[inline_parameter_saved_pair_def] >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem inline_parameter_saved_pair_operands:
  !ops. inline_parameter_saved_pair (p,child,route,snap) (q,pa,proute,psnap) /\
  child.ia_parent = SOME edge ==>
  eval_operands ops edge.ipe_saved = eval_operands ops psnap.ils_state
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  drule_all inline_parameter_saved_pair_operand >>
  disch_then (qspec_then `h` assume_tac) >> simp[]
QED

(* Uniqueness of ia_parent identifies the archived state of the actual call,
   even after arbitrary changes to the active child's snapshot. *)
Theorem inline_parameter_saved_reads_original_child:
  inline_parameter_saved_reads
    (prefix ++ (p,child,route,snap)::(q,pa,proute,psnap)::rest) /\
  inline_original_child C fuel pa.ia_id occurrence call saved r child cr ==>
  (!op. eval_operand op saved = eval_operand op psnap.ils_state) /\
  (!ops. eval_operands ops saved = eval_operands ops psnap.ils_state)
Proof
  strip_tac >> drule inline_parameter_saved_reads_adjacent >> strip_tac >>
  gvs[inline_original_child_def] >>
  metis_tac[inline_parameter_saved_pair_operand,
            inline_parameter_saved_pair_operands]
QED

Theorem inline_parameter_saved_reads_live_parent:
  inline_parameter_saved_reads
    (prefix ++ (p,child,route,snap)::(q,pa,proute,psnap)::rest) /\
  inline_original_child C fuel pa.ia_id occurrence call saved r child cr /\
  inline_owner_storage cert
    (prefix ++ (p,child,route,snap)::(q,pa,proute,psnap)::rest) frame ==>
  inline_tracked_snapshot pa.ia_function pa proute psnap frame /\
  (!op. eval_operand op saved = eval_operand op psnap.ils_state) /\
  (!ops. eval_operands ops saved = eval_operands ops psnap.ils_state)
Proof
  strip_tac >>
  drule_all inline_parameter_saved_reads_original_child >> strip_tac >>
  simp[] >> irule inline_owner_storage_member >>
  goal_assum (drule_at Any) >> qexists `q` >> simp[]
QED
