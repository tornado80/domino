(* Story 111: a one-sided sampling of `dbits_n` closes under
   `seq 0 1 : (#pre); 1: auto => />.`, because `Types.ec` declares
   `op [lossless] dbits_n`. *)

require import AllCore Distr Types.

module L = {
  proc f() : bool = {
    return true;
  }
}.

module R1 = {
  var x : bits_n

  proc f() : bool = {
    x <$ dbits_n;
    return true;
  }
}.

equiv independent_sampling : L.f ~ R1.f : true ==> ={res}.
proof.
  proc.
  seq 0 1 : (#pre); 1: auto => />.
  auto.
qed.

(* A hand-written proof that names `dbits_n_ll` still finds it. *)
lemma dbits_n_ll_is_named : is_lossless dbits_n.
proof. exact dbits_n_ll. qed.
