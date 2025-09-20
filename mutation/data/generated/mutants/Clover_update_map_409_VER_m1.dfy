// Clover_update_map.dfy

method update_map<K(!new), V>(m1: map<K, V>, m2: map<K, V>) returns (r: map<K, V>)
  ensures forall k: K {:trigger k in r} {:trigger k in m2} :: k in m2 ==> k in r
  ensures forall k: K {:trigger k in r} {:trigger k in m1} :: k in m1 ==> k in r
  ensures forall k: K {:trigger m2[k]} {:trigger r[k]} {:trigger k in m2} :: k in m2 ==> r[k] == m2[k]
  ensures forall k: K {:trigger m1[k]} {:trigger r[k]} {:trigger k in m1} {:trigger k in m2} :: !(k in m2) && k in m1 ==> r[k] == m1[k]
  ensures forall k: K {:trigger k in r} {:trigger k in m1} {:trigger k in m2} :: !(k in m2) && !(k in m1) ==> !(k in r)
  decreases m1, m2
{
  r := map k: K {:trigger m1[k]} {:trigger k in m2} {:trigger k in m1.Keys + m2.Keys} | k in m1.Keys + m2.Keys :: if k in m2 then m1[k] else m1[k];
}
