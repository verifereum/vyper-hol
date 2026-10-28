(* TOP-LEVEL: configure -- preserve symbolic selector applications while
   evaluating packaged compiler environments. Concrete selectors still use
   the existing kernel-checked conversion. *)
structure compilerPackagingEvalLib = struct
  open HolKernel boolLib

  fun configure () = let
    val selector = prim_mk_const {Thy="contractABI",Name="function_selector"}
    val rules = evalCompilerBytecodeLib.unique_rules (List.concat (List.concat
      (map (fn (_,entries) => map
        (fn clauses.RRules ths => ths | clauses.Conversion _ => []) entries)
        (computeLib.listItems (computeLib.the_compset ())))))
    val callers = List.filter (fn th =>
      can (find_term (aconv selector)) (rhs (#2(strip_forall(concl th))))
      handle HOL_ERR _ => false) rules
    fun closed_selector tm =
      if null(free_vars tm) andalso null(type_vars_in_term tm) then
        supportedEvalLib.function_selector_conv tm
      else raise Conv.UNCHANGED
  in
    computeLib.del_consts [selector];
    computeLib.add_convs [(selector,2,closed_selector)];
    computeLib.add_funs callers
  end
end
