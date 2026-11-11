(* Storage-only return boundary: pop the child, then update the parent. *)
Theory functionInlinerReturnStorage
Ancestors
  functionInlinerOperationalCuts functionInlinerParameterLifecycle
  functionInlinerContract functionInlinerStackSupports functionInlinerCuts
  venomState list pred_set

Theorem inline_owner_storage_pop:
  inline_owner_storage cert (entry::rest) frame ==>
  inline_owner_storage cert rest frame
Proof
  simp[inline_owner_storage_def, inline_erase_addresses_def,
       inline_suspended_observations_def] >>
  metis_tac[inline_address_stack_pop, inline_addresses_ordered_pop]
QED

Theorem inline_owner_storage_return_writes:
  inline_owner_storage cert
    (child_entry::(p,pa,proute,psnap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  LENGTH call.inst_outputs = LENGTH vals /\
  INJ proute.ir_rename (set call.inst_outputs UNION psnap.ils_defined) UNIV /\
  EVERY (\x. MEM x (cfgTransform$fn_all_vars pa.ia_function) /\
              ~retpc_var pa.ia_function x) call.inst_outputs ==>
  inline_owner_storage cert
    ((p,pa,proute,psnap with <|ils_state :=
       FOLDL (\s (x,w). update_var x w s) psnap.ils_state
         (ZIP (call.inst_outputs,vals));
       ils_defined := set call.inst_outputs UNION psnap.ils_defined|>)::rest)
    (frame with ipf_state :=
       FOLDL (\s (x,w). update_var x w s) frame.ipf_state
         (ZIP (MAP proute.ir_rename call.inst_outputs,vals)))
Proof
  strip_tac >> drule inline_owner_storage_pop >> strip_tac >>
  `set call.inst_outputs = set (MAP FST (ZIP (call.inst_outputs,vals)))` by
    simp[MAP_ZIP] >>
  simp[ZIP_MAP, rich_listTheory.FOLDL_MAP, combinTheory.o_DEF,
       pairTheory.UNCURRY_DEF] >>
  ` (\s pair. update_var (proute.ir_rename (FST pair)) (SND pair) s) =
    (\s (x,w). update_var (proute.ir_rename x) w s)` by
      (simp[FUN_EQ_THM] >> gen_tac >> Cases >> simp[]) >>
  simp[] >> irule inline_owner_storage_writes >>
  qpat_x_assum `set call.inst_outputs = _` kall_tac >>
  simp[MAP_ZIP] >>
  reverse conj_tac >- metis_tac[] >>
  gvs[EVERY_MEM] >> gen_tac >> PairCases_on `e` >>
  strip_tac >> simp[] >>
  `MEM e0 call.inst_outputs` by
    (drule MEM_ZIP >> disch_then (qspec_then `(e0,e1)` mp_tac) >>
     simp[] >> metis_tac[MEM_EL]) >> metis_tac[]
QED

Theorem inline_owner_storage_original_return_writes:
  inliner_input_ok C /\ MEM pa.ia_function C.ctx_functions /\
  MEM call (fn_insts pa.ia_function) /\ call.inst_opcode = INVOKE /\
  inline_owner_storage cert
    (child_entry::(p,pa,proute,psnap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  LENGTH call.inst_outputs = LENGTH vals /\
  INJ proute.ir_rename (set call.inst_outputs UNION psnap.ils_defined) UNIV ==>
  inline_owner_storage cert
    ((p,pa,proute,psnap with <|ils_state :=
       FOLDL (\s (x,w). update_var x w s) psnap.ils_state
         (ZIP (call.inst_outputs,vals));
       ils_defined := set call.inst_outputs UNION psnap.ils_defined|>)::rest)
    (frame with ipf_state :=
       FOLDL (\s (x,w). update_var x w s) frame.ipf_state
         (ZIP (MAP proute.ir_rename call.inst_outputs,vals)))
Proof
  strip_tac >> drule_all inline_call_output_namespace >> strip_tac >>
  irule inline_owner_storage_return_writes >> metis_tac[]
QED

(* Auxiliary invariants are independent of the parent's new live snapshot.
   In particular this does not claim agreement with the stale saved caller. *)
Theorem inline_parameter_return_writes_auxiliary:
  inline_parameter_saved_reads
    ((q,child,croute,csnap)::(p,pa,proute,psnap)::rest) /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners
      ((q,child,croute,csnap)::(p,pa,proute,psnap)::rest)) ==>
  inline_parameter_saved_reads
    ((p,pa,proute,psnap with <|ils_state :=
       FOLDL (\s (x,w). update_var x w s) psnap.ils_state
         (ZIP (call.inst_outputs,vals));
       ils_defined := set call.inst_outputs UNION psnap.ils_defined|>)::rest) /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners
      ((p,pa,proute,psnap with <|ils_state :=
         FOLDL (\s (x,w). update_var x w s) psnap.ils_state
           (ZIP (call.inst_outputs,vals));
         ils_defined := set call.inst_outputs UNION psnap.ils_defined|>)::rest))
Proof
  strip_tac >> drule_all inline_parameter_lifecycle_pop >> strip_tac >>
  irule inline_parameter_lifecycle_head_replace >> metis_tac[]
QED
