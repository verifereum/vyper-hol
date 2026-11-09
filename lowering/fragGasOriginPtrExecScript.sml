(* The joint path lifts memory and pointer checks to one operational run. *)
Theory fragGasOriginPtrExec
Ancestors
  fragGasOriginPtr fragGasOrigin gasPathPtrExec fragGasPathMem fragGasMode
  fragExec fragExecMem ptrSafeRun memSafeRun venomExecSemantics venomExecProofs
  venomState arithmetic list

Theorem gas_origin_ptr_path_exec:
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) marks (r, G', tn') ==>
  ((?t. r = OK t /\ ~t.vs_halted /\
        !fuel out.
          run_from fuel ctx func t = out /\ (!e. out <> Error e) ==>
          ?fuel'. run_from fuel' ctx func s = out /\
            ghost_run fuel' ctx func PG G tn s =
              ghost_run fuel ctx func PG G' tn' t /\
            (mem_safe_run fuel ctx func t ==>
             mem_safe_run fuel' ctx func s) /\
            (ptr_safe_run D lo fuel ctx func PG G' tn' t ==>
             ptr_safe_run D lo fuel' ctx func PG G tn s)) \/
   (exit_result r /\
    ?fuel. run_from fuel ctx func s = r /\
      ghost_run fuel ctx func PG G tn s = (G', tn') /\
      mem_safe_run fuel ctx func s /\
      ptr_safe_run D lo fuel ctx func PG G tn s))
Proof
  strip_tac >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  drule gas_origin_path_erase >> simp[gas_marked_path_def] >>
  disch_then (strip_assume_tac o MATCH_MP gas_path_mem_exec) >>
  drule gas_path_ptr_exec >> strip_tac >>
  gvs[exit_result_def]
  >- (gen_tac >> strip_tac >>
      qpat_x_assum `!fuel. _ ==> ?fuel'. _ /\ ghost_run _ _ _ _ _ _ _ = _ /\ _`
        (qspec_then `fuel` mp_tac) >>
      simp[] >> strip_tac >>
      qexists_tac `fuel'` >> simp[] >> strip_tac >>
      metis_tac[mem_safe_run_all_fuel]) >>
  disj2_tac >>
  metis_tac[mem_safe_run_all_fuel, exit_result_not_error]
QED
