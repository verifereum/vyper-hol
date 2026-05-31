(* Test: what are the variable names after gvs in transfer_sound? *)

val _ = let
  val gvs = fn _ => fn _ => ()
  val Abbr = fn _ => ()
in
  print "Transfer sound obligation from analysis_block_sim_inv_at:\n";
  print "After rpt strip_tac, universals become:\n";
  print "  fuel -> fuel (or fuel' if shadowed)\n";
  print "  ctx' -> ctx'\n";
  print "  idx  -> idx\n";
  print "  s    -> s' (shadowed by outer s)\n";
  print "  s'   -> s'' (shadowed by outer s and transfer's s)\n";
  print "After gvs[Abbr 'sound', ...], sound is unfolded in asms/goal\n";
  print "Variable names depend on whether gvs consumes equalities\n"
end;
