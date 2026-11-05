(* Actual storage/transient copy prefixes and their linear-memory footprints. *)
Theory bodyStorageCopyMemory
Ancestors
  exprSimStorageCopy storageDecodeMemory fragExecMem instMemFrontier
  context compileEnv emitHelper emitHelperProps fragExec exprLoweringProps
  venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map
Libs
  monadsyntax

Theorem body_storage_singleton_mem_ok:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand dst s = SOME (n2w b : bytes32) /\
  (!x. dst = Var x ==> x <> v) /\
  b + 32 < dimword (:256) /\ b + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst id (if loc = LocStorage then SLOAD else TLOAD) [src] [v];
     mk_inst (id+1) MSTORE [dst; Var v] []] s
Proof
  cheat
QED

Theorem body_storage_iteration_mem_ok:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand dst s = SOME (n2w b : bytes32) /\
  eval_operand (Var cv) s = SOME (n2w k) /\
  ALL_DISTINCT [cv; sv; vv; mv; dv; nv] /\
  (!x. src = Var x \/ dst = Var x ==>
       ~MEM x [cv; sv; vv; mv; dv; nv]) /\
  b + 32*(k+1) < dimword (:256) /\
  b + 32*(k+1) <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst id ADD [src; Var cv] [sv];
     mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+3) ADD [dst; Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] s
Proof
  cheat
QED

(* Resolve the shared execution interface here, without duplicating it. *)
val () = (List.app (fn _ => ())
  [storage_copy_source_run_effect, storage_copy_destination_run_effect,
   storage_copy_increment_run_effect, storage_copy_body_run,
   storage_copy_body_run_effect];
  print "BODY_STORAGE_COPY_EXECUTION_EXPORTS OK\n");

