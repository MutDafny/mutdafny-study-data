// Clover_convert_map_key.dfy

method convert_map_key(inputs: map<nat, bool>, f: nat -> nat) returns (r: map<nat, bool>)
  requires forall n1: nat, n2: nat {:trigger f(n2), f(n1)} :: n1 != n2 ==> f(n1) != f(n2)
  ensures forall k: nat {:trigger f(k)} {:trigger k in inputs} :: k in inputs <==> f(k) in r
  ensures forall k: nat {:trigger inputs[k]} {:trigger f(k)} {:trigger k in inputs} :: k in inputs ==> r[f(k)] == inputs[k]
  decreases inputs
{
  r := map k: nat {:trigger inputs[k]} {:trigger f(k)} {:trigger k in inputs} | k in inputs :: -f(k) := inputs[k];
}
