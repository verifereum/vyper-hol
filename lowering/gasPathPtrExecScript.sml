(*
 * S3 piece: a counted pointer-checked path is a pointer-safe run.  The
 * pointer twin of fragGasPathMem's gas_path_mem_exec: a path that goes on
 * at t gives every run from t as a run from s, with the ghost carried
 * along and pointer safety back to s; one that stops gives the run from s
 * that stops there, pointer-safe, with the ghost where it stops.
 *
 * TOP-LEVEL:
 *   gas_path_ptr_exec -- the piece
 *)
Theory gasPathPtrExec
Ancestors
  fragGasPathPtr fragGasPath fragExec ptrSafeRun ptrDiscipline
  venomExecSemantics venomExecProofs venomInstProofs venomState
  arithmetic list

Theorem gas_path_ptr_exec:
  !D lo ctx fn PG G tn s n G' tn' r.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    gas_path ctx fn s n r /\
    ((?t. r = OK t /\ ~t.vs_halted /\
          !fuel out.
            run_from fuel ctx fn t = out /\ (!e. out <> Error e) ==>
            ?fuel'. run_from fuel' ctx fn s = out /\
                    ghost_run fuel' ctx fn PG G tn s =
                      ghost_run fuel ctx fn PG G' tn' t /\
                    (ptr_safe_run D lo fuel ctx fn PG G' tn' t ==>
                     ptr_safe_run D lo fuel' ctx fn PG G tn s)) \/
     (exit_result r /\
      ?fuel. run_from fuel ctx fn s = r /\
             ghost_run fuel ctx fn PG G tn s = (G', tn') /\
             ptr_safe_run D lo fuel ctx fn PG G tn s))
Proof
  cheat
QED
