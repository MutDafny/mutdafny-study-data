// dafny-exercise_tmp_tmpouftptir_filter.dfy

method Filter(a: seq<char>, b: set<char>) returns (c: set<char>)
  ensures forall x: char {:trigger x in c} {:trigger x in b} {:trigger x in a} :: x in a && x in b <==> x in c
  decreases a, b
{
  var setA: set<char> := set x: char {:trigger x in a} | x in a;
  c := setA * b;
}

method TesterFilter()
{
}
