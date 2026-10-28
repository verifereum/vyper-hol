(* Compose existing proof tactics in short slices. Each slice remains subject
   to holbuild's ordinary tactic timeout and creates no evaluation facts. *)
structure compilerProofSliceEvalLib = struct
  fun run step goal = let
    val started = Time.now ()
    fun advance remaining goal =
      if remaining = 0 orelse
          Time.- (Time.now (),started) >= Time.fromReal 0.025 then
        Tactical.ALL_TAC goal
      else Tactical.THEN (step,advance (remaining - 1)) goal
  in advance 64 goal end
end
